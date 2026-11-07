-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_rowBound_concl_transport
-- name    : AaronsonAmbainis.Bridge.rowBound_concl_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:49:05.810786+00:00
-- url     : https://prove2.me/theorems/2578a29a-505a-4b9c-840c-123970345af8
-- title:
--   Bridge: row Bound concl transport
-- statement:
--   The conclusion of `RowBound` transports along an equivalence of index types.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Transport.lean#L61-L75
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Transport.lean#L61-L75

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [DecidableEq ι] [DecidableEq κ]

theorem AaronsonAmbainis.Bridge.rowBound_concl_transport (e : ι ≃ κ) (f : Cube ι → ℝ) (B : ℝ)
    (h : ∃ c : Cube κ → κ → ℝ,
      (∀ x y, |f (fun i => x (e i)) - f (fun i => y (e i))| ≤ ∑ k ∈ diffSet x y, c x k) ∧
      (∀ x, ∑ k, c x k ≤ B)) :
    ∃ c : Cube ι → ι → ℝ,
      (∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) ∧ (∀ x, ∑ i, c x i ≤ B) := by sorry
