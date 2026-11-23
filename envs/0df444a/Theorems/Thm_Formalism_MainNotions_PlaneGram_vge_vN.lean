-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_vN
-- name    : Formalism.MainNotions.PlaneGram.vge_vN
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:36.243884+00:00
-- url     : https://prove2.me/theorems/c469925b-89df-4569-9a07-7674a959f7ef
-- title:
--   Plane Gram: vge v N
-- statement:
--   The Plane Gram construction uses the vge v N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L263-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L263-L265

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

theorem Formalism.MainNotions.PlaneGram.vge_vN (hD : DVRHyp v p) {n : ℕ} (hn : n ≠ 0) : vge v (vN v n) (n : K) := by sorry
