-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_engine
-- name    : Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.engine
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:22:46.669346+00:00
-- url     : https://prove2.me/theorems/5c15b75b-2195-4ad0-8faf-458d356e7a29
-- title:
--   In: engine
-- statement:
--   The In construction uses the engine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L1012-L1085
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L1012-L1085

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
attribute [local fun_prop] mulM_meas invM_meas sgF_meas
set_option maxHeartbeats 800000

theorem Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.engine {μG μN μb μW μW' : Measure (Mt k r)} [SFinite μN] [SFinite μb] [SFinite μW] [SFinite μW'] (T T' : ℝ)
    (G0 : (Fin r → ℂ) → Mt k r) (hG0 : Measurable G0) (ES : ℂ → Mt k r) (hES : Measurable ES) (C1 C2 : ℝ≥0)
    (hIt : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μG = (C1 : ℝ≥0∞) * ∫⁻ c : Fin r → ℂ,
      ENNReal.ofReal (cWeight k r c) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
        f (mulM (mulM (mulM (invM p.1.1, G0 c), p.2), p.1.2)) ∂((μN.prod μN).prod μb))
    (hR : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ m, f m ∂μb = (C2 : ℝ≥0∞) * ∫⁻ ζ : ℂ,
      ENNReal.ofReal (zWeight k T T' ζ) * ∫⁻ p : Mt k r × Mt k r, f (mulM (mulM (invM p.1, ES ζ), p.2)) ∂(μW.prod μW'))
    (hkey : ∀ (c : Fin r → ℂ) (ζ : ℂ) (f : Mt k r → ℝ≥0∞), Measurable f →
      ∫⁻ nn : Mt k r × Mt k r, ∫⁻ hh : Mt k r × Mt k r,
        f (mulM (mulM (mulM (invM nn.1, G0 c), mulM (mulM (invM hh.1, ES ζ), hh.2)), nn.2))
          ∂(μW.prod μW') ∂(μN.prod μN) =
      ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, ES ζ))) ∂((μW.prod μN).prod (μW'.prod μN)))
    (f : Mt k r → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂μG = ((C1 * C2 : ℝ≥0) : ℝ≥0∞) * ∫⁻ q : (Fin r → ℂ) × ℂ,
      ENNReal.ofReal (cWeight k r q.1 * zWeight k T T' q.2) *
        ∫⁻ p : SS k r, f (sgF (p, mulM (G0 q.1, ES q.2))) ∂((μW.prod μN).prod (μW'.prod μN)) := by sorry
