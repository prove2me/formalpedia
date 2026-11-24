-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_cell_meas
-- name    : Formalism.FourierDecayAlt.P.LongWeylElement.cell_meas
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:03:22.549984+00:00
-- url     : https://prove2.me/theorems/0383cf84-27ec-45a9-b166-5c0415c7ac33
-- title:
--   Long Weyl Element: cell meas
-- statement:
--   The Long Weyl Element construction uses the cell meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L801-L804
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L801-L804

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
variable {k r r' : ℕ}

theorem Formalism.FourierDecayAlt.P.LongWeylElement.cell_meas {α : Type*} [MeasurableSpace α] {N T M N' : α → Mt k r} (hN : Measurable N) (hT : Measurable T)
    (hM : Measurable M) (hN' : Measurable N') :
    Measurable (β := Mt k r) (fun t => ((Matrix.of (N t))⁻¹ * Matrix.of (T t) * Matrix.of (M t) * Matrix.of (N' t) : Mat k r)) := by sorry
