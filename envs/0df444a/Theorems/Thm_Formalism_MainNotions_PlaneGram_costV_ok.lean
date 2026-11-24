-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_costV_ok
-- name    : Formalism.MainNotions.PlaneGram.costV_ok
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:37.751256+00:00
-- url     : https://prove2.me/theorems/910a328f-4329-4163-8928-66f122751fd3
-- title:
--   Plane Gram: cost V ok
-- statement:
--   The Plane Gram construction uses the cost V ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L420-L451
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L420-L451

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
open MvPolynomial

theorem Formalism.MainNotions.PlaneGram.costV_ok {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (fam : Set (Finset L))
    (hadd : ∀ S ∈ fam, ∀ (θ : ℝ) (F G : MvPolynomial (L × Fin r) K),
      vala sg S θ F → vala sg S θ G → vala sg S θ (F + G))
    (hsmul : ∀ S ∈ fam, ∀ (θ : ℝ) (a : K) (F : MvPolynomial (L × Fin r) K),
      vala sg S θ F → vala sg S θ (a • F)) :
    CostOK (CostV (K := K) (r := r) sg fam) := by sorry
