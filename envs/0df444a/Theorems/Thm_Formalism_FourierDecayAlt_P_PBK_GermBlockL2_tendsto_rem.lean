-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_GermBlockL2_tendsto_rem
-- name    : Formalism.FourierDecayAlt.P.PBK.GermBlockL2.tendsto_rem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:55:31.924916+00:00
-- url     : https://prove2.me/theorems/d27689f4-f9d9-5f13-9a07-55d076f1a1cd
-- title:
--   Germ Block L2: tendsto rem
-- statement:
--   The Germ Block L2 construction uses the tendsto rem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermFibreKernels.lean#L72-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermFibreKernels.lean#L72-L96

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermFibreKernels
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
variable {ι : Type} {μ : Measure ℂ} {Y : Finset ι} {U A : ι × ℂ → ℂ → H} {N : ℂ → ι → ι → ℂ}

theorem Formalism.FourierDecayAlt.P.PBK.GermBlockL2.tendsto_rem [IsFiniteMeasureOnCompacts μ] [NullSingletonClass μ] (hG : GermBlockL2 μ Y U A N)
    {h h' : ι} (hh : h ∈ Y) (hh' : h' ∈ Y) (σ τ : ℂ) :
    Tendsto (fun x => ∫ D, ⟪U (h, x + σ) D - A (h, x + σ) D, A (h', x + τ) D⟫_ℂ ∂μ) (cocompact ℂ) (𝓝 0) := by sorry
