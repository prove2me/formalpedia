-- Prove2me | Theorems.Thm_Expanders_card_level_succ_le
-- name    : Expanders.card_level_succ_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T15:08:55.926682+00:00
-- url     : https://prove2.me/theorems/1fd3d32c-8cfb-4756-93ad-a1bf2bcc2164
-- title:
--   Expanders: card level succ le
-- statement:
--   Layer growth: the number of vertices of `B` on level `i + 1` is at most `d - 1` times the
--   number on level `i`.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L114-L143
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L114-L143

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] {d k : ℕ} (B : Finset V) (h : V → ℕ)

theorem Expanders.card_level_succ_le (hd : G.IsRegularOfDegree d)
    (hstep : ∀ v ∈ B, ∀ w ∈ B, G.Adj v w → h w ≤ h v + 1)
    (hpar : ∀ v ∈ B, ∃ w ∈ B, G.Adj v w ∧ h w ≤ h v - 1) (i : ℕ) :
    (B.filter (fun v => h v = i + 1)).card ≤ (B.filter (fun v => h v = i)).card * (d - 1) := by sorry
