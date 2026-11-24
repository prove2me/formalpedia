-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_UH
-- name    : Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:26:20.064149+00:00
-- url     : https://prove2.me/theorems/267aada8-d90a-4b22-a76d-3dcb1f2a7237
-- title:
--   Two By One Block: herm UH
-- statement:
--   The Two By One Block construction uses the herm UH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L547-L551
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L547-L551

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH {m : ℕ} {H g : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UH H) (x y : Fin m → ℂ) :
    herm H (g *ᵥ x) (g *ᵥ y) = herm H x y := by sorry
