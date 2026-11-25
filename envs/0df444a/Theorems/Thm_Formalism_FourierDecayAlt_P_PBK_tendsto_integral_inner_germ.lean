-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_integral_inner_germ
-- name    : Formalism.FourierDecayAlt.P.PBK.tendsto_integral_inner_germ
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:27:00.372992+00:00
-- url     : https://prove2.me/theorems/21d52e15-e1e3-5f41-b8e9-d03b125eacb4
-- title:
--   PBK: tendsto integral inner germ
-- statement:
--   The PBK construction uses the tendsto integral inner germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermRealisation.lean#L110-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermRealisation.lean#L110-L182

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockPSDCongr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Formalism.FourierDecayAlt.P.PBK.tendsto_integral_inner_germ {α : Type} {l : Filter α} (μ : Measure ℂ) [IsFiniteMeasureOnCompacts μ]
    [NullSingletonClass μ] (F G : α → ℂ → H) (g : ℂ → ℝ) (hg : MemLp g 2 μ) (B : ℝ)
    (hF : ∀ᶠ x in l, MemLp (F x) 2 μ ∧ ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ B)
    (hG : ∀ᶠ x in l, ∀ᵐ D ∂μ, ‖G x D‖ ≤ g D)
    (hloc : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ x in l, ∀ᵐ D ∂μ, D ∈ K → ‖F x D‖ ≤ δ) :
    Tendsto (fun x => ∫ D, ⟪F x D, G x D⟫_ℂ ∂μ) l (𝓝 0) := by sorry
