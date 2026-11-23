-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_cutM_eq_zero
-- name    : Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.cutM_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:51.013342+00:00
-- url     : https://prove2.me/theorems/cc12fa6e-39b6-4f61-b7d7-10294687a8d0
-- title:
--   Whittaker Vanishing Implies Zero: cut M eq zero
-- statement:
--   The Whittaker Vanishing Implies Zero construction uses the cut M eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L41-L51

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

theorem Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.cutM_eq_zero {s : ℕ} {τ : ℝ} {Z : Mat s} (hτ : 0 < τ) (h : 2 * τ ≤ ‖Z‖) : cutM τ Z = 0 := by sorry
