-- Prove2me | Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_cU_mul_conj
-- name    : Formalism.MainNotions.DIV.HookProducts.RBTie.cU_mul_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:25.799692+00:00
-- url     : https://prove2.me/theorems/02e94a31-eb48-492a-9510-4b96d4301faf
-- title:
--   RBTie: c U mul conj
-- statement:
--   The RBTie construction uses the c U mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieFrame.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieFrame.lean#L125-L127

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
variable (b : Basis ι K V) (XA : InfinitePlace K → Matrix ι ι ℂ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
  (e : (Fin d → K) ≃ₗ[K] V) (v : InfinitePlace K)

theorem Formalism.MainNotions.DIV.HookProducts.RBTie.cU_mul_conj (h : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b XA v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y)
    (hXA : IsUnit (XA v).det) (hX : IsUnit (X v).det) : cU b XA X e v * (cU b XA X e v)ᴴ = 1 := by sorry
