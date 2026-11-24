-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_Tr_first_axis_injective
-- name    : Formalism.IndefR.LatticeTransfer.Lat.Tr.first_axis_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:30.879095+00:00
-- url     : https://prove2.me/theorems/b0d480ac-ead0-4e63-a6e5-2ee27aacfa80
-- title:
--   Tr: first axis injective
-- statement:
--   The Tr construction uses the first axis injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L89-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L89-L101

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

theorem Formalism.IndefR.LatticeTransfer.Lat.Tr.first_axis_injective (h : Tr p₀ p x y c) (a : Fin n → V) (ha : ∀ j, p₀ (a j) = a j)
    (h0 : ∑ j, x j (a j) = 0) : a = 0 := by sorry
