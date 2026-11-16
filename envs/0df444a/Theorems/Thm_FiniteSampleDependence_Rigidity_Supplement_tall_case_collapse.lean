-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_Supplement_tall_case_collapse
-- name    : FiniteSampleDependence.Rigidity.Supplement.tall_case_collapse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:49:22.044519+00:00
-- url     : https://prove2.me/theorems/28939c2b-3760-4379-8636-ba975114a7e3
-- title:
--   Theorem 3.5 — tall-case collapse: for $n>m\ge2$ every $C^1$-extendable (LF-DPI), (IZ) functional vanishes on $\Delta_{n,m}$
-- statement:
--   Let $n>m\ge2$ and let $F$ be a functional on the joint-distribution simplex $\Delta_{n,m}$ that is $C^1$-extendable (Definition 2.2) and satisfies (LF-DPI) and (IZ). Then
--   $$F(U)=0\qquad\text{for every }U\in\Delta_{n,m}.$$
--
--   When the processed variable has more states than the other one, the boundary-regularity condition leaves no nonzero dependence measure. $F$ is an arbitrary functional, not necessarily a polynomial, and no nonnegativity or permutation invariance is assumed; both follow from Lemma 2.1 of the mission.
--
--   Differences from the source:
--   - encoding: a functional F : Δ_{n,m} → ℝ on the simplex → a function on all real n×m matrices, of which only the values on Δ_{n,m} enter; reason: every hypothesis and conclusion reads F only at points of Δ_{n,m} (TU stays in Δ_{n,m}); every functional on Δ_{n,m} extends
--   - encoding: row indices 1..n, column indices 1..m → Fin n and Fin m (zero-based); reason: relabelling of indices; no instance changes
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Theorem 3.5, PDF p. 10 (printed p. 9)

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model

namespace FiniteSampleDependence.Rigidity.Supplement

open Matrix

/-- Theorem 3.5 (Tall-case collapse), PDF p. 10 (printed p. 9). Let `n > m ≥ 2`. Every
`C¹`-extendable functional on `Δ_{n,m}` satisfying (LF-DPI) and (IZ) is identically zero on
`Δ_{n,m}`. -/
theorem tall_case_collapse {n m : ℕ} (hm : 2 ≤ m) (hnm : m < n)
    (F : Matrix (Fin n) (Fin m) ℝ → ℝ) (hC1 : IsC1Extendable F) (hDPI : LFDPI F) (hIZ : IZ F) :
    ∀ U ∈ simplex n m, F U = 0 := by sorry

end FiniteSampleDependence.Rigidity.Supplement
