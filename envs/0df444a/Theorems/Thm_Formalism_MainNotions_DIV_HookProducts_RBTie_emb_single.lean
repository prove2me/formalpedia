-- Prove2me | Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_emb_single
-- name    : Formalism.MainNotions.DIV.HookProducts.RBTie.emb_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:20.910007+00:00
-- url     : https://prove2.me/theorems/95753da6-db70-48b6-8961-733394b6f48a
-- title:
--   RBTie: emb single
-- statement:
--   The RBTie construction uses the emb single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieFrame.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieFrame.lean#L68-L73

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

theorem Formalism.MainNotions.DIV.HookProducts.RBTie.emb_single (v : InfinitePlace K) (k : Fin d) :
    (fun l => v.embedding ((Pi.single k (1 : K) : Fin d → K) l)) = Pi.single k (1 : ℂ) := by sorry
