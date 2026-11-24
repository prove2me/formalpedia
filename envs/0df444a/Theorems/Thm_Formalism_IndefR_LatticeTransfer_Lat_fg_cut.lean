-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_fg_cut
-- name    : Formalism.IndefR.LatticeTransfer.Lat.fg_cut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:11.137645+00:00
-- url     : https://prove2.me/theorems/1099e876-e86a-43b9-9533-a73e752be144
-- title:
--   Lat: fg cut
-- statement:
--   The Lat construction uses the fg cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L62-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L62-L63

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

theorem Formalism.IndefR.LatticeTransfer.Lat.fg_cut {A : Submodule (𝓞 K) V} (hA : A.FG) (p : V →ₗ[K] V) : (cut A p).FG := by sorry
