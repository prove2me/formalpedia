-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_idem_gen
-- name    : Formalism.IndefR.LatticeTransfer.IdempotentLemmas.idem_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:07.704072+00:00
-- url     : https://prove2.me/theorems/b7d374b0-87cc-4ee0-a0f4-cf185f31469f
-- title:
--   Idempotent Lemmas: idem gen
-- statement:
--   The Idempotent Lemmas construction uses the idem gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinrankIntSelf.lean#L172-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinrankIntSelf.lean#L172-L191

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf
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
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.IdempotentLemmas
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem Formalism.IndefR.LatticeTransfer.IdempotentLemmas.idem_gen {V : Type} [AddCommGroup V] [Module K V] {H : Type} [Group H] {_ : Fintype H}
    (a : H → K) (ha : ∀ h k, a h * a k = a (h * k)) (π : H →* Module.End K V)
    (hn : (Nat.card H : K) ≠ 0) :
    ((Nat.card H : K)⁻¹ • ∑ h : H, a h • π h) * ((Nat.card H : K)⁻¹ • ∑ h : H, a h • π h) =
      (Nat.card H : K)⁻¹ • ∑ h : H, a h • π h := by sorry
