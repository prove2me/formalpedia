-- Prove2me | Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_fcoord_e
-- name    : Formalism.MainNotions.DIV.HookProducts.RBTie.fcoord_e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:23.471919+00:00
-- url     : https://prove2.me/theorems/25cf0396-3814-43b9-a706-4a5eb9c16e62
-- title:
--   RBTie: fcoord e
-- statement:
--   The RBTie construction uses the fcoord e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieFrame.lean#L54-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieFrame.lean#L54-L61

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

theorem Formalism.MainNotions.DIV.HookProducts.RBTie.fcoord_e (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K)
    (y : Fin d → K) :
    Formalism.HermitianLatticesTheory.fcoord b XA v (e y) = ((XA v)⁻¹ * cP b e v) *ᵥ (fun l => v.embedding (y l)) := by sorry
