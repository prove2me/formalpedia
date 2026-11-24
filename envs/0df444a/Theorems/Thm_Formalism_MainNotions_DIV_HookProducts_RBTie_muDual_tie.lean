-- Prove2me | Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_muDual_tie
-- name    : Formalism.MainNotions.DIV.HookProducts.RBTie.muDual_tie
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:54:28.461869+00:00
-- url     : https://prove2.me/theorems/b147fdc3-ae87-440f-8a1a-d62e660e1a83
-- title:
--   RBTie: mu Dual tie
-- statement:
--   The RBTie construction uses the mu Dual tie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieMu.lean#L34-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieMu.lean#L34-L94

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieOp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieSlope
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieMu
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

theorem Formalism.MainNotions.DIV.HookProducts.RBTie.muDual_tie (A : Formalism.BasicNotions.HLat K) {n : ℕ} (L : Submodule (𝓞 K) (Fin n → K))
    (XE : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (e : (Fin n → K) ≃ₗ[K] A.V)
    (hlat : A.L = L.map ((e : (Fin n → K) →ₗ[K] A.V).restrictScalars (𝓞 K)))
    (hmet : ∀ v x y, Formalism.HermitianLatticesTheory.majAt A.b A.X v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) XE v x y)
    (hXA : ∀ v, IsUnit (A.X v).det) (hXE : ∀ v, IsUnit (XE v).det) :
    Formalism.HN.muDef (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat L) = A.muDual := by sorry
