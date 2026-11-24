-- Prove2me | Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_harProj_eq_zero_iff
-- name    : Formalism.MainNotions.flipOneThree.Pf.harProj_eq_zero_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:12:31.180244+00:00
-- url     : https://prove2.me/theorems/00d638e5-c7be-4294-a4a4-6bbf74946bf7
-- title:
--   Pf: har Proj eq zero iff
-- statement:
--   The Pf construction uses the har Proj eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/HarProjEqZeroIff.lean#L19-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/HarProjEqZeroIff.lean#L19-L32

import Definitions.Def_Formalism_PolynomialDimension_FinalHar
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_HarProjEqZeroIff
import Theorems.Thm_Formalism_CountingSumsFrames_Top_harProj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf
open Formalism.CountingSumsFrames MvPolynomial

theorem Formalism.MainNotions.flipOneThree.Pf.harProj_eq_zero_iff {K : Type} [Field K] [CharZero K] {k : ℕ} (hk : 1 ≤ k) (p : ℕ) (hp : p.Prime)
    (Ov : ValuationSubring K) (hloc : PLocal Ov.toSubring p) {a b : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k a b) :
    harProj K k a b f = 0 ↔ ∃ G ∈ PolAB K k (a - 1) (b - 1), f = hXY K k * G := by sorry
