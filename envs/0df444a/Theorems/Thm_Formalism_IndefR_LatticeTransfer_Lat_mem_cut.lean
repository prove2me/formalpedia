-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_mem_cut
-- name    : Formalism.IndefR.LatticeTransfer.Lat.mem_cut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:33:14.604395+00:00
-- url     : https://prove2.me/theorems/008ad309-a5ec-4e17-83b7-5ee8bf633d90
-- title:
--   Lat: mem cut
-- statement:
--   The Lat construction uses the mem cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L18-L24

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer Formalism.IndefR.LatticeTransfer.Lat
open Formalism.IndefR.TransferLatticeStatement Formalism.HN Formalism.IndefR.LatticeTransfer
variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [NumberField K]

theorem Formalism.IndefR.LatticeTransfer.Lat.mem_cut {A : Submodule (𝓞 K) V} {p : V →ₗ[K] V} (hp : ∀ a, p (p a) = p a) {a : V} :
    a ∈ cut A p ↔ a ∈ A ∧ p a = a := by sorry
