-- Prove2me | Theorems.Thm_ActuarialValuation_cm1SelectUltimateRate_before
-- name    : ActuarialValuation.cm1SelectUltimateRate_before
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:59:31.422965+00:00
-- url     : https://prove2.me/theorems/56ef4974-8567-4b3d-88a3-1276c92cbe10
-- title:
--   Select, UDD and constant force: cm1SelectUltimateRate_before
-- statement:
--   Before the select duration ends, the selected mortality table supplies the rate. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   t<k\Longrightarrow q_{[x]+t}=q^{S}_{x,t}
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 6. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 3, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), chapters 3 and 8, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing; CM1_new_formula.pdf (user study notes), pages 5–8. Parent topic: CM1 survival probabilities, life tables, UDD/constant force, select mortality, joint and last survivor benefits, reversionary annuities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1SelectUltimateRate

namespace ActuarialValuation

theorem cm1SelectUltimateRate_before (select : ℕ → ℕ → ℝ) (ultimate : ℕ → ℝ) (x k t : ℕ) (h : t < k) : cm1SelectUltimateRate select ultimate x k t = select x t := by sorry

end ActuarialValuation
