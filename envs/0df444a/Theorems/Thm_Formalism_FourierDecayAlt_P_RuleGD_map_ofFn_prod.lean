-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_map_ofFn_prod
-- name    : Formalism.FourierDecayAlt.P.RuleGD.map_ofFn_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:34.010621+00:00
-- url     : https://prove2.me/theorems/28206646-a4f9-4e67-91d7-bb850e69d2ad
-- title:
--   Rule GD: map of Fn prod
-- statement:
--   The Rule GD construction uses the map of Fn prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L67-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L67-L71

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleGD
open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Matrix
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

theorem Formalism.FourierDecayAlt.P.RuleGD.map_ofFn_prod {n : ℕ} (φ : A →+* A) (f : Fin n → A) (hf : ∀ i, φ (f i) = f i) :
    φ (List.ofFn f).prod = (List.ofFn f).prod := by sorry
