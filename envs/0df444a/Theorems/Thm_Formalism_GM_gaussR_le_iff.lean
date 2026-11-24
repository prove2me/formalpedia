-- Prove2me | Theorems.Thm_Formalism_GM_gaussR_le_iff
-- name    : Formalism.GM.gaussR_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:49.66746+00:00
-- url     : https://prove2.me/theorems/8db4a939-3178-473b-9b12-c0f7a41833a2
-- title:
--   GM: gauss R le iff
-- statement:
--   The GM construction uses the gauss R le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GaussRad.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GaussRad.lean#L18-L19

import Definitions.Def_Formalism_MahlerMeasure_StatementD
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GaussRad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
variable {K : Type} [NormedField K]

theorem Formalism.GM.gaussR_le_iff (ρ : NNReal) (P : K[X]) (c : NNReal) :
    gaussR ρ P ≤ c ↔ ∀ k, ‖P.coeff k‖₊ * ρ ^ k ≤ c := by sorry
