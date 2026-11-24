-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_row_of_col
-- name    : Formalism.FourierDecayAlt.P.LongWeylElement.row_of_col
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:18:19.474477+00:00
-- url     : https://prove2.me/theorems/9592dbdf-7103-48b6-b850-3e90dc5306c9
-- title:
--   Long Weyl Element: row of col
-- statement:
--   The Long Weyl Element construction uses the row of col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L390-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L390-L397

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

theorem Formalism.FourierDecayAlt.P.LongWeylElement.row_of_col {m : ℕ} (g H : Matrix (Fin m) (Fin m) ℂ) (i₀ j : Fin m)
    (hc : ∀ p, g p i₀ = if p = i₀ then 1 else 0) : (gᴴ * H * g) i₀ j = (H * g) i₀ j := by sorry
