-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_UnitaryNormCounts_card_inert
-- name    : Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts.card_inert
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:36.558573+00:00
-- url     : https://prove2.me/theorems/2ceea1fe-6f5b-4ed1-a9eb-5bf868e03292
-- title:
--   Unitary Norm Counts: card inert
-- statement:
--   The Unitary Norm Counts construction uses the card inert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardMapEquiv.lean#L93-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardMapEquiv.lean#L93-L116

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardMapEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts
open Matrix
variable {A k : Type*} [CommRing A] [StarRing A] [Field k]
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts.card_inert [Fintype k] (φ : A ≃+* k) (σ : k ≃+* k) (hφ : ∀ a, φ (star a) = σ (φ a))
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2)
    (u : m → A) (hu : ∀ i, star (u i) = u i) (hunit : ∀ i, IsUnit (u i)) :
    Nat.card {X : Matrix m m A // Xᴴ * diagonal u * X = diagonal u} =
      Nat.card {X : Matrix m m k // (X.map σ).transpose * X = 1} := by sorry
