-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_exists_norm_iteratedFDeriv_critCut_le
-- name    : Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.exists_norm_iteratedFDeriv_critCut_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:26.632047+00:00
-- url     : https://prove2.me/theorems/00c85575-8e79-441a-bd4c-eff9d6147d2e
-- title:
--   Whittaker Vanishing Implies Zero: exists norm iterated FDeriv crit Cut le
-- statement:
--   The Whittaker Vanishing Implies Zero construction uses the exists norm iterated FDeriv crit Cut le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L129-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L129-L138

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.exists_norm_iteratedFDeriv_critCut_le (d : ℕ) {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    ∃ C : ℝ, ∀ x : Fin d → ℂ, ‖iteratedFDeriv ℝ j (critCut δ 0) x‖ ≤ C := by sorry
