-- Prove2me | Theorems.Thm_Expanders_top_level_mass_le
-- name    : Expanders.top_level_mass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:09:01.434667+00:00
-- url     : https://prove2.me/theorems/f099df8b-b770-4a0c-bde4-1c5c63e8b315
-- title:
--   Expanders: top level mass le
-- statement:
--   The top layer carries at most a `1/(k+1)` fraction of the mass `∑_{v ∈ B} q ^ h v`, when
--   `q (d - 1) = 1`.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L147-L188
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L147-L188

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

theorem Expanders.top_level_mass_le (hd1 : 1 ≤ d) (hd : G.IsRegularOfDegree d)
    (hB : ∀ v ∈ B, h v ≤ k)
    (hstep : ∀ v ∈ B, ∀ w ∈ B, G.Adj v w → h w ≤ h v + 1)
    (hpar : ∀ v ∈ B, ∃ w ∈ B, G.Adj v w ∧ h w ≤ h v - 1) {q : ℝ} (hq : 0 ≤ q)
    (hqd : q * ((d : ℝ) - 1) = 1) :
    ((k : ℝ) + 1) * ∑ v ∈ B.filter (fun v => h v = k), q ^ h v ≤ ∑ v ∈ B, q ^ h v := by sorry
