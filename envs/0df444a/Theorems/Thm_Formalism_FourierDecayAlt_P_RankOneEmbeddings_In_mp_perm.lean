-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_mp_perm
-- name    : Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.mp_perm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:22:49.950624+00:00
-- url     : https://prove2.me/theorems/4d2623f7-55bc-4f00-9fab-818833b007e2
-- title:
--   In: mp perm
-- statement:
--   The In construction uses the mp perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L902-L915
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L902-L915

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
variable {k r : ℕ}
attribute [local fun_prop] mulM_meas invM_meas

theorem Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.mp_perm {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (a : Measure α) (b : Measure β) (c : Measure γ) (d : Measure δ) [SFinite a] [SFinite b] [SFinite c] [SFinite d] :
    MeasurePreserving (fun x : (α × β) × (γ × δ) => ((x.2.1, x.1.1), (x.2.2, x.1.2)))
      ((a.prod b).prod (c.prod d)) ((c.prod a).prod (d.prod b)) := by sorry
