-- Prove2me | Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_cQ_mul_cP
-- name    : Formalism.MainNotions.DIV.HookProducts.RBTie.cQ_mul_cP
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:32.495342+00:00
-- url     : https://prove2.me/theorems/5bbff637-1e77-4243-850d-017fedf6701b
-- title:
--   RBTie: c Q mul c P
-- statement:
--   The RBTie construction uses the c Q mul c P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieFrame.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieFrame.lean#L49-L52

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField Module
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.DIV Formalism.MainNotions.DIV.HookProducts Formalism.MainNotions.DIV.HookProducts.RBTie
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

theorem Formalism.MainNotions.DIV.HookProducts.RBTie.cQ_mul_cP (b : Basis ι K V) (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K) : cQ b e v * cP b e v = 1 := by sorry
