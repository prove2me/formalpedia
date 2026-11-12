-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_coordinate_transfers_unused_state
-- name    : FiniteSampleDependence.Rigidity.coordinate_transfers_unused_state
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T08:49:10.275164+00:00
-- url     : https://prove2.me/theorems/5156c9fe-30fc-4b71-a15d-e0c2e3a8bf6c
-- title:
--   Lemma 3.2 — coordinate transfers at an unused state
-- statement:
--   Let $n,m\ge2$. Suppose $U\in\Delta_{n,m}$ has a zero row $r$ and $U_{i\alpha}>0$ for every $i\ne r$ and every $\alpha$. Let $F$ satisfy (LF-DPI). Then every $C^1$ extension $(\Omega,\widetilde F)$ of $F$ (Definition 2.2) satisfies
--   $$\partial_{i\alpha}\widetilde F(U)=\partial_{j\alpha}\widetilde F(U)$$
--   for all distinct rows $i,j\ne r$ and every column $\alpha$.
--
--   Within each column, the occupied rows have equal partial derivatives at such a point; the empty row serves as a common reference. Mass transfers between occupied rows therefore do not change $F$ to first order.
--
--   Differences from the source:
--   - encoding: standing assumption n, m ≥ 2 (Section 2, 'Throughout, n, m ≥ 2') → explicit hypotheses 2 ≤ n and 2 ≤ m; reason: the section's standing assumption written into the binders
--   - encoding: a functional F : Δ_{n,m} → ℝ on the simplex → a function F on all real n×m matrices, of which only the values on Δ_{n,m} enter the hypotheses and conclusion; reason: every hypothesis and conclusion quantifies over U ∈ Δ_{n,m} (and TU, M_{ij}U, QU stay in Δ_{n,m}), so the values off the simplex are irrelevant; every functional on Δ_{n,m} extends
--   - encoding: row indices 1..n, column indices 1..m → Fin n and Fin m (zero-based); reason: relabelling of indices; no instance changes
--   - encoding: F is C¹-extendable, and the conclusion holds for every C¹ extension of F → the hypothesis 'F is C¹-extendable' is not written separately; the theorem takes an arbitrary C¹ extension (Ω, G) of F; reason: the existence of the extension that the conclusion is about already makes F C¹-extendable, so the separate hypothesis excludes nothing
--   - encoding: partial derivative ∂_{iα} F̃(U) → fderiv ℝ G U applied to the matrix unit E_{iα}; reason: G is C¹ on the open set Ω ∋ U, hence differentiable at U, so fderiv is its true derivative and its value on E_{iα} is the partial derivative
--   - encoding: a C¹ function F̃ : Ω → ℝ on an open Ω ⊆ ℝ^{n×m} → a total function G on Fin n → Fin m → ℝ, constrained only on Ω, with a matrix U placed there by Matrix.of.symm; reason: any function on Ω extends by 0 off Ω, and ContDiffOn on Ω and fderiv at points of the open set Ω read only values on Ω; all norms on the finite-dimensional ambient space are equivalent, so C¹ does not depend on the sup norm Lean uses
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Lemma 3.2, PDF p. 9 (printed p. 8)

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model

namespace FiniteSampleDependence.Rigidity

/-- Lemma 3.2 (Coordinate transfers at an unused state). Let `U ∈ Δ_{n,m}` have zero row `r` and
be strictly positive outside that row. If `F` satisfies (LF-DPI), then every `C¹` extension `G : Ω → ℝ` of `F` (Definition 2.2) satisfies
`∂_{iα} G(U) = ∂_{jα} G(U)` for all distinct `i, j ≠ r` and every column `α`. -/
theorem coordinate_transfers_unused_state {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (F : Matrix (Fin n) (Fin m) ℝ → ℝ) (hF : LFDPI F)
    (U : Matrix (Fin n) (Fin m) ℝ) (hU : U ∈ simplex n m) (r : Fin n)
    (hr : ∀ α, U r α = 0) (hpos : ∀ i α, i ≠ r → 0 < U i α)
    (Ω : Set (Ambient n m)) (G : Ambient n m → ℝ) (hG : IsC1Extension F Ω G) :
    ∀ i j : Fin n, i ≠ r → j ≠ r → i ≠ j → ∀ α : Fin m,
      fderiv ℝ G (Matrix.of.symm U) (entryDir i α) =
        fderiv ℝ G (Matrix.of.symm U) (entryDir j α) := by sorry

end FiniteSampleDependence.Rigidity
