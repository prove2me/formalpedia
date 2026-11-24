-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_aPsi_basis
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_aPsi_basis
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:32:13.056158+00:00
-- url     : https://prove2.me/theorems/e73b12a1-a819-4956-8877-813378980421
-- title:
--   Column Families: qb a Psi basis
-- statement:
--   The Column Families construction uses the qb a Psi basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationMaximalQuotient.lean#L83-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationMaximalQuotient.lean#L83-L92

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_aPsi_basis (b : Basis ι R V) (s : Set ι) (c : Basis ↥s R W) (i : ι) (hi : i ∈ s) :
    qb_aPsi b s c (b i) = c ⟨i, hi⟩ := by sorry
