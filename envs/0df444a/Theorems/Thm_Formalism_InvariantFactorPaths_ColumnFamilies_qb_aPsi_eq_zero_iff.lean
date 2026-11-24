-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_aPsi_eq_zero_iff
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_aPsi_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:31:20.305342+00:00
-- url     : https://prove2.me/theorems/48b7f218-d511-4ad0-81d2-3855b6fab464
-- title:
--   Column Families: qb a Psi eq zero iff
-- statement:
--   The Column Families construction uses the qb a Psi eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationMaximalQuotient.lean#L94-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationMaximalQuotient.lean#L94-L100

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationMaximalQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Module
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
variable {R : Type*} [CommRing R] {V A B W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup W] [Module R W] {ι κ : Type*} [DecidableEq κ] {φ : κ → Type*}

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_aPsi_eq_zero_iff (b : Basis ι R V) (s : Set ι) (c : Basis ↥s R W) (x : V) :
    qb_aPsi b s c x = 0 ↔ ∀ i ∈ s, b.repr x i = 0 := by sorry
