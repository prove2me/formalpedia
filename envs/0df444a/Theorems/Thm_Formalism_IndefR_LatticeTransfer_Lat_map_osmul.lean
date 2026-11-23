-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_map_osmul
-- name    : Formalism.IndefR.LatticeTransfer.Lat.map_osmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:28.733743+00:00
-- url     : https://prove2.me/theorems/94caa450-2b5e-485c-b8fd-d143f8fe3d5b
-- title:
--   Lat: map osmul
-- statement:
--   The Lat construction uses the map osmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L66-L68

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

theorem Formalism.IndefR.LatticeTransfer.Lat.map_osmul {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (p : V →ₗ[K] W) (d : 𝓞 K) (a : V) : p (d • a) = d • p a := by sorry
