-- Prove2me | Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_gram_tie
-- name    : Formalism.MainNotions.DIV.HookProducts.RBTie.gram_tie
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:40:31.833083+00:00
-- url     : https://prove2.me/theorems/30f2400c-877d-4211-abac-f619631036e3
-- title:
--   RBTie: gram tie
-- statement:
--   The RBTie construction uses the gram tie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieFrame.lean#L75-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieFrame.lean#L75-L85

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

theorem Formalism.MainNotions.DIV.HookProducts.RBTie.gram_tie (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (e : (Fin d → K) ≃ₗ[K] V)
    (h : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b XA v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y)
    (v : InfinitePlace K) :
    ((XA v)⁻¹ * cP b e v)ᴴ * ((XA v)⁻¹ * cP b e v) = ((X v)⁻¹)ᴴ * (X v)⁻¹ := by sorry
