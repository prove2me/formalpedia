-- Prove2me | Theorems.Thm_Formalism_MainNotions_DIV_HookProducts_RBTie_mem_dualLat_iff
-- name    : Formalism.MainNotions.DIV.HookProducts.RBTie.mem_dualLat_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:56.590854+00:00
-- url     : https://prove2.me/theorems/a33b667d-5833-4154-9eb1-1561847f98f4
-- title:
--   RBTie: mem dual Lat iff
-- statement:
--   The RBTie construction uses the mem dual Lat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieMu.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieMu.lean#L17-L19

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

theorem Formalism.MainNotions.DIV.HookProducts.RBTie.mem_dualLat_iff {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (A : Submodule (𝓞 K) V) (f : Module.Dual K V) :
    f ∈ Formalism.HN.dualLat A ↔ ∀ x ∈ A, f x ∈ Set.range (algebraMap (𝓞 K) K) := by sorry
