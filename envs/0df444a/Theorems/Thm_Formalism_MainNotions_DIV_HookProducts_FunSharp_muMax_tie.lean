-- Prove2me | Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_FunSharp_muMax_tie
-- name    : Formalism.MainNotions.DIV.HookProducts.FunSharp.muMax_tie
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:53.119134+00:00
-- url     : https://prove2.me/theorems/87fa5bf2-723a-412d-b687-fc64b7d2784f
-- title:
--   Fun Sharp: mu Max tie
-- statement:
--   The Fun Sharp construction uses the mu Max tie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/NormAtEqSqrtMajAt.lean#L64-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/NormAtEqSqrtMajAt.lean#L64-L123

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieSlope
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_NormAtEqSqrtMajAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.DIV Formalism.MainNotions.DIV.HookProducts Formalism.MainNotions.DIV.HookProducts.FunSharp
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.MainNotions.DIV.HookProducts.FunSharp.muMax_tie (A : Formalism.BasicNotions.HLat K) {n : ℕ} (L : Submodule (𝓞 K) (Fin n → K))
    (XE : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (e : (Fin n → K) ≃ₗ[K] A.V)
    (hlat : A.L = L.map ((e : (Fin n → K) →ₗ[K] A.V).restrictScalars (𝓞 K)))
    (hmet : ∀ v x y, Formalism.HermitianLatticesTheory.majAt A.b A.X v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) XE v x y) :
    Formalism.HN.muMaxDef (Pi.basisFun K (Fin n)) XE L = A.muMax := by sorry
