-- Prove2me | Theorems.Thm_ActuarialAnnuities_term_fully_guaranteed
-- name    : ActuarialAnnuities.term_fully_guaranteed
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:02:23.558989+00:00
-- url     : https://prove2.me/theorems/dcc6b732-c2af-4a43-9af1-38ae1c2ef4e4
-- title:
--   Term Fully Guaranteed
-- statement:
--   A fully guaranteed activated annuity equals commencement survival times matching annuity-certain.
--
--   Mathematical relation:
--
--   $$
--   g\ge n\Longrightarrow V=S_h(a)V_{\text{certain}}
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 159, Guaranteed annuities (Chapter 5, section 5.9). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bCertainPV

namespace ActuarialAnnuities

theorem term_fully_guaranteed (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hg : n ≤ g) : bSurvivalPV h a n g delta v b p = bSurvival h p a * bCertainPV h a n delta v b := by sorry

end ActuarialAnnuities
