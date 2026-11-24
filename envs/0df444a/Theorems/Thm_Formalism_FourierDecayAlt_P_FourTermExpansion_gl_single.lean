-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_gl_single
-- name    : Formalism.FourierDecayAlt.P.FourTermExpansion.gl_single
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:14:40.950125+00:00
-- url     : https://prove2.me/theorems/88e75984-104d-4f32-9b6b-92011955241a
-- title:
--   Four Term Expansion: gl single
-- statement:
--   The Four Term Expansion construction uses the gl single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L165-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L165-L172

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.FourTermExpansion.gl_single {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 2 Φ g) (hgG : g ∈ GV k r)
    (a b c d : Fin (2 * r + k + 1)) :
    EZ (Msg k r a b) (EZ (Msg k r c d) Φ) g - EZ (Msg k r c d) (EZ (Msg k r a b) Φ) g =
      (if b = c then (1 : ℂ) else 0) • EZ (Msg k r a d) Φ g -
        (if d = a then (1 : ℂ) else 0) • EZ (Msg k r c b) Φ g := by sorry
