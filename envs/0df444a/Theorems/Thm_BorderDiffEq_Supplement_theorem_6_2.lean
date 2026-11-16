-- Prove2me | Theorems.Thm_BorderDiffEq_Supplement_theorem_6_2
-- name    : BorderDiffEq.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:00:17.141438+00:00
-- url     : https://prove2.me/theorems/64d87d03-6159-4bf1-bbff-0abee4c7a1cc
-- title:
--   Theorem 6.2 — border $\text{Ext-}\Sigma^{k}\wedge^e\mathcal D_{\text{low-deg}}(\delta,\Delta)$ has depth-6 formulas of size $s^{O(k^2(\Delta+k\delta))}$
-- statement:
--   Let $F$ be a field of characteristic zero, $k,e\in\mathbb N$, and let $f\in\overline{\text{Ext-}\Sigma^{k}\wedge^e\mathcal D_{\text{low-deg}}(\delta,\Delta)}$, approximated by $\sum_iq_iP_i^{e_i}$ with $\deg P_i\le\delta$, $\deg q_i\le\Delta$, $1\le e_i\le e$ and total size at most $s$. Then $f$ can be computed by a depth-6 formula of size $s^{O(k^2(\Delta+k\delta))}$.
--
--   Precisely: there is an absolute $C$ such that $f$ is computed by a formula over $F$ of depth at most $6$ and size at most
--   $$
--   (s+1)^{C\,k^2(\Delta+k\delta)} .
--   $$
--
--   With $q_i=1$ this gives Theorem 2.4; the multipliers $q_i$ make the class closed under the differential-equation method, which the reconstruction algorithm uses.
--
--   Differences from the source:
--   - generalization: border constants in $F(\epsilon)$ and $f+\epsilon g$ with $g\in F[\epsilon][x]$ → constants in $F((\epsilon))$ and $f+\epsilon S$ with $S\in F[[\epsilon]][x]$ (the published `IsEpsApprox`); reason: $F(\epsilon)\subset F((\epsilon))$ and $F[\epsilon]\subset F[[\epsilon]]$, so every presentation of the paper is one here; the statement covers the paper's
--   - reading: $s$ (not defined in the statement) → the total size $\sum_i(\mathrm{size}(q_i)+\mathrm{size}(P_i)+e_i)\le s$; reason: the proof says "total size at most $s$" and "$e\le s$" (p.48); p.8 counts exponents in the size
--   - generalization: $\mathrm{size}(P)$ of a sum of monomials (undefined in the paper) → `spSize P` $=\sum_{m\in\mathrm{supp}P}(1+\#\mathrm{vars}(m))$; reason: at most the usual gate-and-wire count of the sum-of-monomials representation, so the size-bounded class contains the paper's for any standard size
--   - generalization: sums of $k$ terms → sums of at most $k$ terms; reason: padding with zero terms costs size, so the at-most-$k$ class can be larger; it contains the paper's class
--   - encoding: $s^{O(k^2(\Delta+k\delta))}$ → $(s+1)^{Ck^2(\Delta+k\delta)}$, one absolute $C$; reason: reading of $O(\cdot)$; avoids a degenerate claim at $s\le1$
--   - encoding: variables $x_1,\dots,x_n$ → `Fin n` (0-indexed); reason: Lean convention; same instances
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Theorem 6.2, p.48; proof pp.48–50

import Mathlib
import Definitions.Def_BorderDiffEq_Supplement_InBorderExtLowDeg
import Definitions.Def_BorderDiffEq_Supplement_Formula

namespace BorderDiffEq.Supplement

/-- **Theorem 6.2 (debordering the extended low-degree class as a depth-6 formula)** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits
via Differential Equations*, manuscript (STOC 2027 submission),
Theorem 6.2, p.48; proof pp.48–50). Let `k, e ∈ ℕ` and let `f ∈ cl(Ext-Σ^k ∧^e D_low-deg(δ, Δ))`.
Then `f` can be computed by a depth-6 formula. The resulting formula size is `s^{O(k²(Δ+kδ))}`.

**Formalization Note.** `s` is the total size of the approximating circuit,
`∑ᵢ (size(qᵢ) + size(Pᵢ) + eᵢ) ≤ s` (`InBorderExtLowDeg`; the statement leaves `s` undefined, the
proof says "total size at most `s`" and "`e ≤ s`"). `s^{O(k²(Δ+kδ))}` is `(s + 1)^{C·k²(Δ+kδ)}`,
one absolute `C`. The formula is over `F` (constants in `F`, no division), of depth at most `6`. -/
theorem theorem_6_2 : ∃ C : ℕ, ∀ (F : Type) [Field F] [CharZero F] (n k e δ Δ s : ℕ)
    (f : MvPolynomial (Fin n) F), InBorderExtLowDeg F n k e δ Δ s f →
    ∃ φ : Formula F (Fin n), φ.depth ≤ 6 ∧ φ.size ≤ (s + 1) ^ (C * (k ^ 2 * (Δ + k * δ))) ∧
      φ.eval = f := by sorry

end BorderDiffEq.Supplement
