-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_col_iff
-- name    : Formalism.FourierDecayAlt.P.LongWeylElement.lev_col_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:16:59.208954+00:00
-- url     : https://prove2.me/theorems/1a7087d3-4a92-40e3-9566-dcc7eb822f12
-- title:
--   Long Weyl Element: lev col iff
-- statement:
--   The Long Weyl Element construction uses the lev col iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L339-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L339-L353

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}

theorem Formalism.FourierDecayAlt.P.LongWeylElement.lev_col_iff (g : Mat k r') (t : Fin (2 * r' + k + 1)) :
    (∀ p, ιLev k 1 r' g p (levPos k 1 r' t) = if p = levPos k 1 r' t then 1 else 0) ↔
      ∀ s, g s t = if s = t then 1 else 0 := by sorry
