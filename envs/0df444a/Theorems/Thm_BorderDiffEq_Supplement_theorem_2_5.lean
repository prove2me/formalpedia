-- Prove2me | Theorems.Thm_BorderDiffEq_Supplement_theorem_2_5
-- name    : BorderDiffEq.Supplement.theorem_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:57:02.285162+00:00
-- url     : https://prove2.me/theorems/f667df10-1182-4cd3-a17a-854e2cb5340d
-- title:
--   Theorem 2.5 — ABPs for borders of sums of powers of structured polynomials (Table 2)
-- statement:
--   Let $F$ be a field of characteristic zero, $n,k,d\ge1$, and let $f\in F[x_1,\dots,x_n]$ have degree at most $d$. Then:
--   1. if $f\in\overline{\Sigma^{[k]}\wedge\mathcal D}$ with $\mathcal D$ the polynomials of degree at most $\delta$, then $f$ has an ABP of size $\mathrm{poly}\bigl(d,k,(n+1)^{k^2\delta}\bigr)$;
--   2. if $\mathcal D$ is the polynomials whose partial derivative space has dimension at most $\lambda$, the ABP has size $\mathrm{poly}\bigl(n^k,d,k,\lambda^{3k^2}\bigr)$;
--   3. if $\mathcal D=\mathrm{roABP}_\pi(w,R)$ with one order $\pi$ for all bases, the ABP has size $\mathrm{poly}\bigl(n^k,d,k,R,(2w)^{k^2}\bigr)$.
--
--   Precisely: there is one absolute $C$ such that the three ABP sizes are at most
--   $$
--   (d+k+(n+1)^{k^2\delta}+1)^C,\qquad (n^k+d+k+\lambda^{3k^2}+1)^C,\qquad (n^k+d+k+R+(2w)^{k^2}+1)^C .
--   $$
--   The bases are polynomials over $F((\epsilon))$ whose constraints (degree, partial derivative dimension, roABP) hold over $F((\epsilon))$; the ABP is over $F$ with affine edge labels, and its size is its number of vertices.
--
--   For constant $k$ (and $\delta$ in row 1) all three borders lie in VBP when the parameters of the bases are polynomially bounded.
--
--   Differences from the source:
--   - generalization: border constants in $F(\epsilon)$ and $f+\epsilon g$ with $g\in F[\epsilon][x]$ → constants in $F((\epsilon))$ and $f+\epsilon S$ with $S\in F[[\epsilon]][x]$ (the published `IsEpsApprox`); reason: $F(\epsilon)\subset F((\epsilon))$ and $F[\epsilon]\subset F[[\epsilon]]$, so every presentation of the paper is one here; the statement covers the paper's
--   - encoding: sums of $k$ terms → sums of at most $k$ terms; reason: every class used contains $0$ and $0^1=0$, so padding with zero terms gives the same class
--   - encoding: $\mathrm{poly}(a,b,\dots)$ → $(a+b+\dots+1)^C$ with one absolute $C$ for all rows; reason: reading of $\mathrm{poly}$
--   - encoding: partial derivative space of dimension at most $\lambda$ → the published `hasBoundedPartials P λ` (rank over $F((\epsilon))$ of the span of all iterated partial derivatives, order $0$ included); reason: Definition 4.18; same condition
--   - encoding: ABP (size = number of vertices) → the published `BorderDiffEq.ABP` with affine labels over $F$; reason: Definition 4.8; same model
--   - encoding: variables $x_1,\dots,x_n$ → `Fin n` (0-indexed); reason: Lean convention; same instances
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Theorem 2.5 and Table 2, p.8; Theorem 6.1, p.45

import Mathlib
import Definitions.Def_BorderDiffEq_ABP
import Definitions.Def_BorderDiffEq_Supplement_InBorderSumPow
import Definitions.Def_DerivationHitting_Commutative_PolynomialData
import Definitions.Def_BorderDiffEq_Supplement_InRoABP

namespace BorderDiffEq.Supplement

open BorderDiffEq
open DerivationHitting.Commutative (hasBoundedPartials)

/-- **Theorem 2.5 (debordering sums of powers of structured polynomials)** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits
via Differential Equations*, manuscript (STOC 2027 submission), Theorem 2.5 and
Table 2, p.8; follows from Theorem 6.1, §6.2). Let `n, k, d ≥ 1` be integers, and let
`f ∈ F[x₁, …, xₙ]` have degree at most `d`. For each class `D` in Table 2, if
`f ∈ cl(Σ^{[k]} ∧ D)`, then `f` is computed by an ABP of the stated size:
1. polynomials of degree at most `δ`: `poly(d, k, (n+1)^{k²δ})`;
2. polynomials whose partial derivative space has dimension at most `λ`: `poly(n^k, d, k, λ^{3k²})`;
3. `roABP_π(w, R)`, with one order `π` for all bases: `poly(n^k, d, k, R, (2w)^{k²})`.

**Formalization Note.** `poly(a, b, …)` is `(a + b + … + 1)^C` with one absolute `C` (for all three
rows) chosen before the field and every parameter. The bases are polynomials over `F((ε))` and
their constraints are read over `F((ε))` (`InBorderSumPow`); in row 1 the bases have no size bound.
The output is a base `ABP` over `F` (affine labels, size = number of vertices). The condition `∂dim P ≤ λ` is the published `DerivationHitting.Commutative.hasBoundedPartials P λ`:
the rank over `F((ε))` of the span of all iterated partial derivatives of `P`, order `0` included
(Definition 4.18). -/
theorem theorem_2_5 : ∃ C : ℕ, ∀ (F : Type) [Field F] [CharZero F] (n k d : ℕ)
    (f : MvPolynomial (Fin n) F), 1 ≤ n → 1 ≤ k → 1 ≤ d → f.totalDegree ≤ d →
    (∀ δ : ℕ, InBorderSumPow F n k (fun P => P.totalDegree ≤ δ) f →
      ∃ A : ABP F (Fin n), A.eval = f ∧ A.size ≤ (d + k + (n + 1) ^ (k ^ 2 * δ) + 1) ^ C) ∧
    (∀ lam : ℕ, InBorderSumPow F n k (fun P => hasBoundedPartials P lam) f →
      ∃ A : ABP F (Fin n), A.eval = f ∧ A.size ≤ (n ^ k + d + k + lam ^ (3 * k ^ 2) + 1) ^ C) ∧
    (∀ (π : Equiv.Perm (Fin n)) (w R : ℕ),
      InBorderSumPow F n k (InRoABP (LaurentSeries F) n π w R) f →
      ∃ A : ABP F (Fin n), A.eval = f ∧
        A.size ≤ (n ^ k + d + k + R + (2 * w) ^ (k ^ 2) + 1) ^ C) := by sorry

end BorderDiffEq.Supplement
