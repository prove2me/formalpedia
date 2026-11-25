-- Prove2me | Theorems.Thm_ErdosGirth_exists_good_graph
-- name    : ErdosGirth.exists_good_graph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:53.151154+00:00
-- url     : https://prove2.me/theorems/142550ec-02c6-4da4-a4f4-adbdd060744a
-- title:
--   Erdos Girth: exists good graph
-- statement:
--   **First-moment step.** If the expected number of short cycles is small compared to `m` and
--   the expected number of independent `t`-sets is small, some graph on `Fin m` has a set `D` of fewer
--   than `m / 2` vertices meeting every cycle of length at most `g`, and no independent `t`-set.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L276-L328
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L276-L328

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
open Classical

theorem ErdosGirth.exists_good_graph (m g t : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hm : 0 < m)
    (h : 2 / m * ∑ ℓ ∈ range (g + 1), ((m : ℝ) * p) ^ ℓ + m.choose t * (1 - p) ^ t.choose 2 < 1) :
    ∃ G : SimpleGraph (Fin m), ∃ D : Finset (Fin m), 2 * D.card < m ∧
      (∀ u (c : G.Walk u u), c.IsCycle → c.length ≤ g → u ∈ D) ∧
      ∀ T : Finset (Fin m), T.card = t → ¬ G.IsIndepSet (T : Set (Fin m)) := by sorry
