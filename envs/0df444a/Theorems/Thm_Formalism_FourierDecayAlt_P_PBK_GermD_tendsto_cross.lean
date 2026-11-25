-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_GermD_tendsto_cross
-- name    : Formalism.FourierDecayAlt.P.PBK.GermD.tendsto_cross
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:43:22.066466+00:00
-- url     : https://prove2.me/theorems/e1b894cd-0d5f-42d1-9c59-56c482501044
-- title:
--   Germ D: tendsto cross
-- statement:
--   The Germ D construction uses the tendsto cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoRatioPow.lean#L77-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoRatioPow.lean#L77-L121

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemLpBzOfSup
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralInnerGermMoving
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoRatioPow
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
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type} {s : ℕ} {β ε : ℂ} {Y : Finset ι} {ut : ι → ℂ → ℂ → H} {bt : ι → ℂ → H} {SS : ℝ}

theorem Formalism.FourierDecayAlt.P.PBK.GermD.tendsto_cross (hG : GermD s β ε Y ut bt SS) {h h' : ι} (hh : h ∈ Y) (hh' : h' ∈ Y) (a b : ℂ) :
    Tendsto (fun x => ∫ c, ⟪cvec s (fun x D => ut h x D - mainD s β ε (bt h) x D) (x + a) c,
      cvec s (fun x D => mainD s β ε (bt h') x D) (x + b) c⟫_ℂ) (cocompact ℂ) (𝓝 0) := by sorry
