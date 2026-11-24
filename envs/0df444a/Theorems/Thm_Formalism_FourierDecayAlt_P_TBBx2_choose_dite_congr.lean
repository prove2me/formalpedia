-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_choose_dite_congr
-- name    : Formalism.FourierDecayAlt.P.TBBx2.choose_dite_congr
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:54:58.651453+00:00
-- url     : https://prove2.me/theorems/2ffaeca8-0d0c-47eb-909c-f36480892995
-- title:
--   TBBx2: choose dite congr
-- statement:
--   The TBBx2 construction uses the choose dite congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L12-L17

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2
open MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ENNReal
noncomputable section
open Classical

theorem Formalism.FourierDecayAlt.P.TBBx2.choose_dite_congr {α E : Type*} [Zero E] (P Q : α → Prop) (hPQ : P = Q) (f g : α → E)
    [Decidable (∃ θ, P θ)] [Decidable (∃ θ, Q θ)]
    (hfg : ∀ θ, P θ → f θ = g θ) :
    (if h : ∃ θ, P θ then f h.choose else 0) = (if h : ∃ θ, Q θ then g h.choose else 0) := by sorry
