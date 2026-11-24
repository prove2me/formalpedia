-- Prove2me | Theorems.Thm_Formalism_L2_SG_FoldBound_tsum_transversal
-- name    : Formalism.L2.SG.FoldBound.tsum_transversal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:36.04023+00:00
-- url     : https://prove2.me/theorems/35c7bb96-89b1-40e3-a7e8-a6bf8bfac63e
-- title:
--   Fold Bound: tsum transversal
-- statement:
--   The Fold Bound construction uses the tsum transversal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/FoldBound.lean#L34-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/FoldBound.lean#L34-L63

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.FoldBound

theorem Formalism.L2.SG.FoldBound.tsum_transversal {G : Type*} [Group G] (Γ S : Subgroup G) (hSΓ : S ≤ Γ) (D : Set G)
    (hD : IsRightTransversal Γ S D) (φ : G → ℝ≥0∞) :
    ∑' δ : D, ∑' s : S, φ ((δ : G)⁻¹ * (s : G)) = ∑' γ : Γ, φ (γ : G) := by sorry
