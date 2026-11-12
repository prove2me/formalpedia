-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_row_cone_vanishing
-- name    : FiniteSampleDependence.Rigidity.row_cone_vanishing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T08:49:19.249745+00:00
-- url     : https://prove2.me/theorems/761f9ca3-fe4e-40cc-b863-ec0c1e96799a
-- title:
--   Lemma 4.2 — row-cone vanishing
-- statement:
--   Let $n,m\ge2$. If $F$ is $C^1$-extendable and satisfies (LF-DPI) and (IZ) on $\Delta_{n,m}$, then $F(U)=0$ for every $U\in\Delta_{n,m}$ one of whose rows is a nonnegative linear combination of the others: if for some row $k$ there are $\lambda_i\ge0$ ($i\ne k$) with
--   $$U_{k\bullet}=\sum_{i\ne k}\lambda_iU_{i\bullet},$$
--   then $F(U)=0$.
--
--   Coefficients may be zero. This provides an open set of rank-deficient matrices on which every admissible functional vanishes, which drives the algebraic part of the proof.
--
--   Differences from the source:
--   - encoding: standing assumption n, m ≥ 2 (Section 2, 'Throughout, n, m ≥ 2') → explicit hypotheses 2 ≤ n and 2 ≤ m; reason: the section's standing assumption written into the binders
--   - encoding: a functional F : Δ_{n,m} → ℝ on the simplex → a function F on all real n×m matrices, of which only the values on Δ_{n,m} enter the hypotheses and conclusion; reason: every hypothesis and conclusion quantifies over U ∈ Δ_{n,m} (and TU, M_{ij}U, QU stay in Δ_{n,m}), so the values off the simplex are irrelevant; every functional on Δ_{n,m} extends
--   - encoding: row indices 1..n, column indices 1..m → Fin n and Fin m (zero-based); reason: relabelling of indices; no instance changes
--   - encoding: coefficients λ_i for the rows i ≠ k → a vector c : Fin n → ℝ, nonnegative everywhere, of which only the entries i ≠ k are used (the sum runs over univ.erase k); reason: the entry c k is unused and can be set to 0, so the same row combinations are described
--   - encoding: a C¹ function F̃ : Ω → ℝ on an open Ω ⊆ ℝ^{n×m} → a total function G on Fin n → Fin m → ℝ, constrained only on Ω, with a matrix U placed there by Matrix.of.symm; reason: any function on Ω extends by 0 off Ω, and ContDiffOn on Ω and fderiv at points of the open set Ω read only values on Ω; all norms on the finite-dimensional ambient space are equivalent, so C¹ does not depend on the sup norm Lean uses
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Lemma 4.2, PDF p. 11 (printed p. 10)

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model

namespace FiniteSampleDependence.Rigidity

/-- Lemma 4.2 (Row-cone vanishing). If `F` is `C¹`-extendable and satisfies (LF-DPI) and (IZ),
then `F(U) = 0` whenever one row of `U ∈ Δ_{n,m}` is a nonnegative linear combination of the
other rows. -/
theorem row_cone_vanishing {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (F : Matrix (Fin n) (Fin m) ℝ → ℝ) (hC1 : IsC1Extendable F) (hF : LFDPI F) (hIZ : IZ F)
    (U : Matrix (Fin n) (Fin m) ℝ) (hU : U ∈ simplex n m) (k : Fin n)
    (hcone : ∃ c : Fin n → ℝ, (∀ i, 0 ≤ c i) ∧
      ∀ α, U k α = ∑ i ∈ Finset.univ.erase k, c i * U i α) :
    F U = 0 := by sorry

end FiniteSampleDependence.Rigidity
