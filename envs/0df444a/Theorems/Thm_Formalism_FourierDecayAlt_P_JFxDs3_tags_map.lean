-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs3_tags_map
-- name    : Formalism.FourierDecayAlt.P.JFxDs3.tags_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:15:18.16503+00:00
-- url     : https://prove2.me/theorems/36d7141d-c0b6-4222-96e5-63643087055b
-- title:
--   JFx Ds3: tags map
-- statement:
--   The JFx Ds3 construction uses the tags map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselDomainMeasurable.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselDomainMeasurable.lean#L16-L23

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JDomBoundOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxDs3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.JFxDs3.tags_map (φ : Bool × Mat k r → Bool × Mat k r) :
    ∀ l : List (Bool × Mat k r), (∀ y ∈ l, (φ y).1 = y.1) → (l.map φ).map Prod.fst = l.map Prod.fst := by sorry
