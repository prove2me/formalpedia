-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_Tr_yx_sum
-- name    : Formalism.IndefR.LatticeTransfer.Lat.Tr.yx_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:13.146477+00:00
-- url     : https://prove2.me/theorems/bb67f238-e2c3-41f2-a4e9-58e9f481c191
-- title:
--   Tr: yx sum
-- statement:
--   The Tr construction uses the yx sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L84-L87

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

theorem Formalism.IndefR.LatticeTransfer.Lat.Tr.yx_sum (h : Tr p₀ p x y c) (a : Fin n → V) (ha : ∀ j, p₀ (a j) = a j) (i : Fin n) :
    y i (∑ j, x j (a j)) = ∑ j, c i j • a j := by sorry
