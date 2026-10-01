-- Prove2me | Theorems.Thm_Apery_main_estimate
-- name    : Apery.main_estimate
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T11:24:42.914894+00:00
-- url     : https://prove2.me/theorems/f58426e7-d5fc-4010-97d0-6c44ec0af19e
-- title:
--   Small positive integer-polynomial values at ζ(5)
-- statement:
--   There exists a real constant $c>0$ such that every sufficiently large natural number $n$ admits an integer polynomial $Q_n$ satisfying
--   $$Q_n=c'_nF_n\quad\text{for some }c'_n\in\mathbb Q_{>0},\qquad\deg Q_n=37n,$$
--   and
--   $$0<Q_n(z_5)<e^{-cn^2}.$$
--   The scalar-multiple equality is equality of polynomials after mapping integer coefficients to rational coefficients. The constant $c$ is independent of $n$. This is the exact strength of the repository's main estimate: existence of a positive decay rate, without requiring the paper's rate $139/5$.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/MainEstimate.lean#L64-L98

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceValue

open Polynomial Filter Topology MeasureTheory

namespace Apery

theorem main_estimate :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∃ Q : ℤ[X],
      (∃ c' : ℚ, 0 < c' ∧ Q.map (Int.castRingHom ℚ) = C c' * F n) ∧
      Q.natDegree = 37 * n ∧
      0 < aeval zeta5 Q ∧ aeval zeta5 Q < Real.exp (-c * (n : ℝ) ^ 2) := by sorry

end Apery
