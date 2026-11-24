-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StrictBoxOrder_sup_pres
-- name    : Formalism.FourierDecayAlt.P.StrictBoxOrder.sup_pres
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:53:11.022825+00:00
-- url     : https://prove2.me/theorems/b1ced1c7-2a38-4af4-922a-127b76e2a04f
-- title:
--   Strict Box Order: sup pres
-- statement:
--   The Strict Box Order construction uses the sup pres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictBoxOrder.lean#L189-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictBoxOrder.lean#L189-L196

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictBoxOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StrictBoxOrder
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Formalism.FourierDecayAlt.P.StrictBoxOrder.sup_pres {ι : Type} (f : Module.End ℂ V) (F : ι → Submodule ℂ V) (p : ι → Prop)
    (h : ∀ j, ∀ v ∈ F j, f v ∈ F j) : ∀ v ∈ ⨆ (j) (_ : p j), F j, f v ∈ ⨆ (j) (_ : p j), F j := by sorry
