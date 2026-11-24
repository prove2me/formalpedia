-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
-- name    : Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.key
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:47:19.45249+00:00
-- url     : https://prove2.me/theorems/1da0a04f-9e29-4e71-8eaa-0de0e82f2ef4
-- title:
--   In: key
-- statement:
--   The In construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L926-L978
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L926-L978

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

theorem Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.key {z z' : Vc k r} {μW μN μW' : Measure (Mt k r)} [SFinite μW] [SFinite μN] [SFinite μW']
    (UF : UWbFacts) (hW : IsHaarOn (UWset k r z) μW) (hW' : IsHaarOn (UWset k r z') μW')
    (hc : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN) (hc' : ∀ h ∈ UWset k r z', μN.map (conjM h) = μN)
    (g0 E : Mt k r) (hcomm : ∀ m ∈ UWb k r, m * (Matrix.of g0 : Mat k r) = (Matrix.of g0 : Mat k r) * m)
    (f : Mt k r → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ nn : Mt k r × Mt k r, ∫⁻ hh : Mt k r × Mt k r,
        f (mulM (mulM (mulM (invM nn.1, g0), mulM (mulM (invM hh.1, E), hh.2)), nn.2)) ∂(μW.prod μW') ∂(μN.prod μN) =
      ∫⁻ p : SS k r, f (sgF (p, mulM (g0, E))) ∂((μW.prod μN).prod (μW'.prod μN)) := by sorry
