-- Prove2me | Theorems.Thm_BorderDiffEq_Supplement_theorem_6_1
-- name    : BorderDiffEq.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:59:38.333765+00:00
-- url     : https://prove2.me/theorems/f5762db8-41dc-4304-9116-7dc8974e6ae9
-- title:
--   Theorem 6.1 — ABPs for the border of $\text{Ext-}\Sigma^{[k]}\wedge^e\mathcal D$, small-pd and roABP bases (Table 5)
-- statement:
--   Let $F$ be a field of characteristic zero, $k,e\in\mathbb N$, and let $f\in\overline{\text{Ext-}\Sigma^{[k]}\wedge^e\mathcal D(c_1,c_2)}$ have degree at most $d$, where the summands are $q_iP_i^{e_i}$ with $1\le e_i\le e$. Then $f$ can be computed by an ABP of size:
--   1. for $\mathcal D_{\text{small-pd}}(\lambda,\Gamma)$ ($\partial\dim P_i\le\lambda$, $\partial\dim q_i\le\Gamma$): $\mathrm{poly}\bigl(n^k,d,k,\Gamma^{3k}\lambda^{3k^2}\bigr)$;
--   2. for $\mathcal D_{\text{roABP}}((w_1,R_1),(w_2,R_2))$ ($P_i\in\mathrm{roABP}(w_1,R_1)$, $q_i\in\mathrm{roABP}(w_2,R_2)$), common and any order: $\mathrm{poly}\bigl(n^k,d,k,w_2^k(2w_1)^{O(k^2)},R_1R_2\bigr)$.
--
--   Precisely: there are absolute constants $C,C'$ such that the ABP sizes are at most
--   $$
--   (n^k+d+k+\Gamma^{3k}\lambda^{3k^2}+1)^C\quad\text{and}\quad (n^k+d+k+w_2^k(2w_1)^{C'k^2}+R_1R_2+1)^C .
--   $$
--   The roABP row is stated for one common order $\pi$ of all $P_i$ and $q_i$; the any-order class is contained in each common-order class, so it is covered.
--
--   Theorem 6.1 yields rows 2 and 3 of Theorem 2.5 (take $q_i=1$).
--
--   Differences from the source:
--   - generalization: border constants in $F(\epsilon)$ and $f+\epsilon g$ with $g\in F[\epsilon][x]$ → constants in $F((\epsilon))$ and $f+\epsilon S$ with $S\in F[[\epsilon]][x]$ (the published `IsEpsApprox`); reason: $F(\epsilon)\subset F((\epsilon))$ and $F[\epsilon]\subset F[[\epsilon]]$, so every presentation of the paper is one here; the statement covers the paper's
--   - encoding: sums of $k$ terms → sums of at most $k$ terms; reason: every class used contains $0$ and $0^1=0$, so padding with zero terms gives the same class
--   - reading: $d$ in Table 5 (not introduced in the statement) → $\deg f\le d$; reason: the proof fixes "$\deg f\le d$" (p.45)
--   - encoding: "both common and any order" → common order $\pi$ for all $P_i,q_i$; reason: an any-order roABP is in $\mathrm{roABP}_\pi$ for every $\pi$, so the any-order row is the instance of the common-order row
--   - encoding: $\mathrm{poly}(\cdot)$ and the inner $O(k^2)$ → $(\dots+1)^C$ and $C'k^2$, two absolute constants; reason: reading of the asymptotic notation
--   - encoding: $\partial\dim$ at most $\lambda$, $\Gamma$ → the published `hasBoundedPartials`; reason: Definition 4.18; same condition
--   - encoding: variables $x_1,\dots,x_n$ → `Fin n` (0-indexed); reason: Lean convention; same instances
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Theorem 6.1 and Table 5, p.45; proof pp.45–47; classes (29), pp.37–38

import Mathlib
import Definitions.Def_BorderDiffEq_ABP
import Definitions.Def_BorderDiffEq_Supplement_InBorderExt
import Definitions.Def_DerivationHitting_Commutative_PolynomialData
import Definitions.Def_BorderDiffEq_Supplement_InRoABP

namespace BorderDiffEq.Supplement

open BorderDiffEq
open DerivationHitting.Commutative (hasBoundedPartials)

/-- **Theorem 6.1 (debordering the extended class as an ABP)** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits
via Differential Equations*, manuscript (STOC 2027 submission), Theorem 6.1 and Table 5,
p.45; proof pp.45–47). Let `k, e ∈ ℕ`, assume `F` is a field of characteristic zero and let
`f ∈ cl(Ext-Σ^{[k]} ∧^e D(c₁, c₂))` where `D` is either `D_small-pd` or `D_roABP`. Then `f` can be
computed by an ABP, of size (with `deg f ≤ d`, as fixed in the proof):
1. `D_small-pd(λ, Γ)` (`∂dim Pᵢ ≤ λ`, `∂dim qᵢ ≤ Γ`): `poly(n^k, d, k, Γ^{3k} λ^{3k²})`;
2. `D_roABP((w₁, R₁), (w₂, R₂))` (`Pᵢ ∈ roABP(w₁, R₁)`, `qᵢ ∈ roABP(w₂, R₂)`), common and any order:
   `poly(n^k, d, k, w₂^k (2w₁)^{O(k²)}, R₁R₂)`.

**Formalization Note.** `poly(a, b, …)` is `(a + b + … + 1)^C` and the inner `O(k²)` is `C'·k²`, two
absolute constants chosen before the field and every parameter. The roABP row is stated for a
common order `π` of all `Pᵢ` and `qᵢ`; the any-order class is contained in it (take any `π`), so it
is covered. Bases and multipliers are polynomials over `F((ε))` with their constraints read over
`F((ε))`; the exponents satisfy `1 ≤ eᵢ ≤ e`. The ABP is a base `ABP` over `F`. The condition `∂dim P ≤ λ` is the published `DerivationHitting.Commutative.hasBoundedPartials P λ`:
the rank over `F((ε))` of the span of all iterated partial derivatives of `P`, order `0` included
(Definition 4.18). -/
theorem theorem_6_1 : ∃ C C' : ℕ, ∀ (F : Type) [Field F] [CharZero F] (n k e d : ℕ)
    (f : MvPolynomial (Fin n) F), f.totalDegree ≤ d →
    (∀ lam Γ : ℕ,
      InBorderExt F n k e (fun P => hasBoundedPartials P lam) (fun q => hasBoundedPartials q Γ)
        f →
      ∃ A : ABP F (Fin n), A.eval = f ∧
        A.size ≤ (n ^ k + d + k + Γ ^ (3 * k) * lam ^ (3 * k ^ 2) + 1) ^ C) ∧
    (∀ (π : Equiv.Perm (Fin n)) (w₁ R₁ w₂ R₂ : ℕ),
      InBorderExt F n k e (InRoABP (LaurentSeries F) n π w₁ R₁)
        (InRoABP (LaurentSeries F) n π w₂ R₂) f →
      ∃ A : ABP F (Fin n), A.eval = f ∧
        A.size ≤ (n ^ k + d + k + w₂ ^ k * (2 * w₁) ^ (C' * k ^ 2) + R₁ * R₂ + 1) ^ C) := by sorry

end BorderDiffEq.Supplement
