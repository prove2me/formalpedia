-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_top_finsum
-- name    : Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.top_finsum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:43:53.481665+00:00
-- url     : https://prove2.me/theorems/74825f35-6ae9-4278-8194-6a84abe8ade0
-- title:
--   Finite Sum Local Expansion: top finsum
-- statement:
--   The Finite Sum Local Expansion construction uses the top finsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteSumLocalExpansion.lean#L39-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteSumLocalExpansion.lean#L39-L55

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.top_finsum (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (Φ : ι → Mat k r → E) {g : Mat k r} (hg : g ∈ GV k r) (h : ∀ i ∈ s, Loc 1 (Φ i) g)
    (v : ℂ) (a b : Fin (2 * r + k + 1)) :
    Top (FourTermExpansion.LT M) v a b (fun z => ∑ i ∈ s, c i • Φ i z) g = ∑ i ∈ s, c i • Top (FourTermExpansion.LT M) v a b (Φ i) g := by sorry
