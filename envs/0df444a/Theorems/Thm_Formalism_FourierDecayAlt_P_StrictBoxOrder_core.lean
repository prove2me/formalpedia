-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StrictBoxOrder_core
-- name    : Formalism.FourierDecayAlt.P.StrictBoxOrder.core
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:53:20.751814+00:00
-- url     : https://prove2.me/theorems/1cc04f56-d089-41e6-b608-24ed21f0e125
-- title:
--   Strict Box Order: core
-- statement:
--   The Strict Box Order construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictBoxOrder.lean#L79-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictBoxOrder.lean#L79-L187

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictBoxOrder
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_core

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

theorem Formalism.FourierDecayAlt.P.StrictBoxOrder.core (hESM : ExistsSingMax) (hCS : CapSing) (hSR : SubRel) (hTW : TopWeightSing) (hDM : DualMinor)
    (hST : SpanTop) (hMO : MultOne) [FiniteDimensional ℂ V] {n : ℕ}
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (hgl : GlRel E) (hirr : Irr E)
    (m : Fin n → ℂ) (hm : SDec m) (O : Submodule ℂ V) (hO : Stab (subA E) O)
    (hS : Stab (subA E) (CapSp (subA E) m)) (hOq : ∀ w, ∀ v ∈ O, qdet (subA E) w v ∈ O)
    (hdis : Disjoint (CapSp (subA E) m) O) (htop : CapSp (subA E) m ⊔ O = ⊤)
    (S' : Submodule ℂ V) (hS'le : S' ≤ CapSp (subA E) m) (hS' : Stab (subA E) S') (hne : S' ≠ ⊥) :
    S' = CapSp (subA E) m := by sorry
