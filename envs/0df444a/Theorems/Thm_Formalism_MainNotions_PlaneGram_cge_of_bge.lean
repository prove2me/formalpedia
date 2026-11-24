-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_of_bge
-- name    : Formalism.MainNotions.PlaneGram.cge_of_bge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:18.208081+00:00
-- url     : https://prove2.me/theorems/57f3cd04-b330-4b71-9311-708881f03b49
-- title:
--   Plane Gram: cge of bge
-- statement:
--   The Plane Gram construction uses the cge of bge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L553-L566
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L553-L566

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
variable {v} {p : ℕ} [CharZero K]

theorem Formalism.MainNotions.PlaneGram.cge_of_bge (hD : DVRHyp v p) {L : Type} [Fintype L] {r : ℕ} {d : L → ℕ} {a : ℝ}
    {F : MvPolynomial (L × Fin r) K} (hF : F ∈ PolK K r d) (h : bge v a F) :
    cge v (a - vN v (∏ i, (d i).factorial) / 2) F := by sorry
