-- Prove2me | Theorems.Thm_Aggmetrics_exemplar_invariant_iff_constant_mbar
-- name    : Aggmetrics.exemplar_invariant_iff_constant_mbar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:52:40.411571+00:00
-- url     : https://prove2.me/theorems/c4fc6853-d4c7-4225-90ba-f5b6fe31aa6e
-- title:
--   Aggmetrics: exemplar invariant iff constant mbar
-- statement:
--   **Proposition 7: exemplar-averaging's invariance boundary.**
--
--   Given population shares over label-configuration types and each type's conditional mean
--   `mbar`, the exemplar mixture `∑ τ, share τ * mbar τ` is invariant to the population shares
--   — for *every* pair of valid share distributions — if and only if `mbar` is constant across
--   types.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/Basic.lean#L169-L188
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/Basic.lean#L169-L188

import Mathlib
import Definitions.Def_Aggmetrics_Basic
set_option autoImplicit true
open Finset
open Aggmetrics

theorem Aggmetrics.exemplar_invariant_iff_constant_mbar {k : ℕ} (hk : 0 < k) (mbar : Fin k → ℝ) :
    (∀ share1 share2 : Fin k → ℝ,
      (∀ τ, 0 ≤ share1 τ) → (∑ τ, share1 τ = 1) →
      (∀ τ, 0 ≤ share2 τ) → (∑ τ, share2 τ = 1) →
      ∑ τ, share1 τ * mbar τ = ∑ τ, share2 τ * mbar τ)
    ↔ (∀ τ1 τ2, mbar τ1 = mbar τ2) := by sorry
