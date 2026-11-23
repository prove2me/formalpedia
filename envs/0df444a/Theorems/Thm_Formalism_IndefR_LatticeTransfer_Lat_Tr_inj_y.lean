-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_Tr_inj_y
-- name    : Formalism.IndefR.LatticeTransfer.Lat.Tr.inj_y
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:55.902302+00:00
-- url     : https://prove2.me/theorems/ce2e39c2-5fea-4fd3-8eec-1c4271cab6cb
-- title:
--   Tr: inj y
-- statement:
--   The Tr construction uses the inj y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L103-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L103-L105

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
variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {n : ℕ}
variable {p₀ p : V →ₗ[K] V} {x y : Fin n → V →ₗ[K] V} {c : Matrix (Fin n) (Fin n) K}

theorem Formalism.IndefR.LatticeTransfer.Lat.Tr.inj_y (h : Tr p₀ p x y c) (a : V) (ha : p a = a) (h0 : ∀ i, y i a = 0) : a = 0 := by sorry
