-- Prove2me | Theorems.Thm_Formalism_FX_rectRes_edge
-- name    : Formalism.FX.rectRes_edge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:12.970467+00:00
-- url     : https://prove2.me/theorems/97d7bd90-feae-471c-bd3a-364376e84364
-- title:
--   FX: rect Res edge
-- statement:
--   The FX construction uses the rect Res edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/RectResidue.lean#L89-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/RectResidue.lean#L89-L114

import Definitions.Def_Formalism_LFunctionBounds_ExpSumLowerBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.FX

theorem Formalism.FX.rectRes_edge (g G : ℂ → ℂ) (P : Finset ℂ) (b : ℂ → ℂ) (γ : ℝ → ℂ) (a c : ℝ)
    (hγ : Continuous γ) (hG : ContinuousOn (fun t => G (γ t)) (Set.uIcc a c))
    (hP : ∀ t ∈ Set.uIcc a c, ∀ p ∈ P, γ t ≠ p)
    (hg : ∀ w : ℂ, w ∉ P → g w = G w + ∑ p ∈ P, b p / (w - p)) :
    ∫ t in a..c, g (γ t) =
      (∫ t in a..c, G (γ t)) + ∑ p ∈ P, b p * ∫ t in a..c, 1 / (γ t - p) := by sorry
