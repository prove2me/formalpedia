-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_aT_apply
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_aT_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:31:19.821108+00:00
-- url     : https://prove2.me/theorems/443e1854-3732-4723-8596-713f211c035c
-- title:
--   Column Families: qb a T apply
-- statement:
--   The Column Families construction uses the qb a T apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationMaximalQuotient.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationMaximalQuotient.lean#L75-L78

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_aT_apply (bA : ∀ k, Basis (φ k) R A) (bB : Basis κ R B) (x : Σ k, φ k) :
    qb_aT bA bB x = bA x.1 x.2 ⊗ₜ bB x.1 := by sorry
