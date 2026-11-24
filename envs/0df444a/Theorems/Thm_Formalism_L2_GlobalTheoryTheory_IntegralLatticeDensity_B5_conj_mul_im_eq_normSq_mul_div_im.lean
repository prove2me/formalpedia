-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_conj_mul_im_eq_normSq_mul_div_im
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.conj_mul_im_eq_normSq_mul_div_im
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:35.061807+00:00
-- url     : https://prove2.me/theorems/f1f64438-3729-4bc8-b27b-17a43813c842
-- title:
--   B5: conj mul im eq norm Sq mul div im
-- statement:
--   The B5 construction uses the conj mul im eq norm Sq mul div im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/NormArea.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/NormArea.lean#L10-L15

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_Jacobi
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_NormArea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.conj_mul_im_eq_normSq_mul_div_im (a b : ℂ) (ha : a ≠ 0) :
    ((starRingEnd ℂ) a * b).im = Complex.normSq a * (b / a).im := by sorry
