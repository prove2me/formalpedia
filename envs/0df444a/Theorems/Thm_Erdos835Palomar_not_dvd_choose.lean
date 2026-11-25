-- Prove2me | Theorems.Thm_Erdos835Palomar_not_dvd_choose
-- name    : Erdos835Palomar.not_dvd_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:12:15.242275+00:00
-- url     : https://prove2.me/theorems/7faf80fa-027e-4a07-accf-f4c1fcf75ba5
-- title:
--   Erdos835 Palomar: not dvd choose
-- statement:
--   If a prime `p < k + 1` divides `k + 1`, then `k + 1` does not divide `(k + p).choose p`.
--
--   Source: https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L72-L91
-- source:
--   https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L72-L91

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib
public import Definitions.Def_Erdos835Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open Erdos835Palomar

theorem Erdos835Palomar.not_dvd_choose (k p : ℕ) (hp : p.Prime) (hpk : p ∣ k + 1) (hlt : p < k + 1) :
    ¬ (k + 1) ∣ (k + p).choose p := by sorry
