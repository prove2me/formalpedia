-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_nu_hyp
-- name    : Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.nu_hyp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:22:00.219117+00:00
-- url     : https://prove2.me/theorems/2f97c9f6-a63d-45b6-9d49-7db8981f1a35
-- title:
--   R1: nu hyp
-- statement:
--   The R1 construction uses the nu hyp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L512-L551
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L512-L551

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.nu_hyp (CWb : ClosedWb) (CW : ClosedW) (UF : UWbFacts) (z z' : Vc k r)
    {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s) (hsu : ∀ ζ, (s ζ)ᴴ * Hb k * s ζ = Hb k)
    {μW μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW) [SFinite μW] [SFinite μW']
    (f : Mt k r → ℝ≥0∞) (hf : Measurable f) (G : Vc k r → ℝ≥0∞) (hG : Measurable G)
    (hFG : ∀ m ∈ UWb k r, (∫⁻ h', f (mulM (m, h')) ∂μW') = G (m *ᵥ z')) (b : Mat k r) (hb : b ∈ UWb k r) :
    ∫⁻ m, f (lmulM b m) ∂(nu z z' s μW μW') = ∫⁻ v, G (b *ᵥ v) ∂(hypMeas k r z z' s μW) := by sorry
