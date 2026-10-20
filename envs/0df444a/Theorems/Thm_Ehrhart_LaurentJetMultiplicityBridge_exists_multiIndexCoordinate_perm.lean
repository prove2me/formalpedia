-- Prove2me | Theorems.Thm_Ehrhart_LaurentJetMultiplicityBridge_exists_multiIndexCoordinate_perm
-- name    : Ehrhart.LaurentJetMultiplicityBridge.exists_multiIndexCoordinate_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:44.97552+00:00
-- url     : https://prove2.me/theorems/581c0110-a4a8-4588-980c-8537046f4acc
-- title:
--   Ehrhart.LaurentJetMultiplicityBridge.exists_multiIndexCoordinate_perm
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | EhrhartVolumeInequality | external Lean 4.33.1 validation; bundle SHA256 7150ea60aef8441515028279454832b05d0f964f3966505d147b2c1d8afe9763

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.LaurentJetMultiplicityBridge
open Set Filter Module
open scoped BigOperators Topology

theorem Ehrhart.LaurentJetMultiplicityBridge.exists_multiIndexCoordinate_perm {n : ℕ}
    (α : Fin n → ℕ)
    (q : Fin (∑ i, α i) → Fin n)
    (hq : ∀ i : Fin n,
      Fintype.card {a : Fin (∑ i, α i) // q a = i} = α i) :
    ∃ σ : Equiv.Perm (Fin (∑ i, α i)),
      ∀ a, q a =
        AdaptedBergmanBasis.multiIndexCoordinate α (σ a) := by sorry
