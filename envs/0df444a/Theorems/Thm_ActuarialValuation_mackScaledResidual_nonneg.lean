-- Prove2me | Theorems.Thm_ActuarialValuation_mackScaledResidual_nonneg
-- name    : ActuarialValuation.mackScaledResidual_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:28:34.331038+00:00
-- url     : https://prove2.me/theorems/bf75817b-6042-48f9-a511-7729f339de17
-- title:
--   Residual dispersion and one-step uncertainty: mackScaledResidual_nonneg
-- statement:
--   Mack residual scaling requires positive observed cumulative claims. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   C>0\Rightarrow e^2/C\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackScaledResidual

namespace ActuarialValuation

theorem mackScaledResidual_nonneg (a b exposure : ℝ) (h : 0 < exposure) : 0 ≤ mackScaledResidual a b exposure := by sorry

end ActuarialValuation
