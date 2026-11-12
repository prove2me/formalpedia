-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_zero_row_vanishing
-- name    : FiniteSampleDependence.Rigidity.zero_row_vanishing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T08:49:34.558204+00:00
-- url     : https://prove2.me/theorems/fcfb694d-129f-49df-b9ad-269f5e7a9041
-- title:
--   Theorem 3.3 — zero-row vanishing
-- statement:
--   Let $n,m\ge2$. If $F:\Delta_{n,m}\to\mathbb R$ is $C^1$-extendable and satisfies (LF-DPI) and (IZ), then
--   $$F(U)=0\qquad\text{for every } U\in\Delta_{n,m}\text{ that has a zero row}.$$
--
--   No positivity of the remaining entries is assumed. This is the zero-row clause of the paper's Theorem A; it is where boundary regularity enters, and Shannon mutual information escapes it only because it is not $C^1$-extendable.
--
--   Differences from the source:
--   - encoding: a functional F : Δ_{n,m} → ℝ on the simplex → a function F on all real n×m matrices, of which only the values on Δ_{n,m} enter the hypotheses and conclusion; reason: every hypothesis and conclusion quantifies over U ∈ Δ_{n,m} (and TU, M_{ij}U, QU stay in Δ_{n,m}), so the values off the simplex are irrelevant; every functional on Δ_{n,m} extends
--   - encoding: row indices 1..n, column indices 1..m → Fin n and Fin m (zero-based); reason: relabelling of indices; no instance changes
--   - encoding: a C¹ function F̃ : Ω → ℝ on an open Ω ⊆ ℝ^{n×m} → a total function G on Fin n → Fin m → ℝ, constrained only on Ω, with a matrix U placed there by Matrix.of.symm; reason: any function on Ω extends by 0 off Ω, and ContDiffOn on Ω and fderiv at points of the open set Ω read only values on Ω; all norms on the finite-dimensional ambient space are equivalent, so C¹ does not depend on the sup norm Lean uses
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Theorem 3.3, PDF p. 9 (printed p. 8)

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model

namespace FiniteSampleDependence.Rigidity

/-- Theorem 3.3 (Zero-row vanishing). Let `n, m ≥ 2`. If `F : Δ_{n,m} → ℝ` is `C¹`-extendable
and satisfies (LF-DPI) and (IZ), then `F(U) = 0` whenever `U ∈ Δ_{n,m}` has a zero row. -/
theorem zero_row_vanishing {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (F : Matrix (Fin n) (Fin m) ℝ → ℝ) (hC1 : IsC1Extendable F) (hF : LFDPI F) (hIZ : IZ F)
    (U : Matrix (Fin n) (Fin m) ℝ) (hU : U ∈ simplex n m) (hzero : ∃ r, ∀ α, U r α = 0) :
    F U = 0 := by sorry

end FiniteSampleDependence.Rigidity
