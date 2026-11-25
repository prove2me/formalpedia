-- Prove2me | Theorems.Thm_ErdosGirth_exists_of_deletion
-- name    : ErdosGirth.exists_of_deletion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:41.519592+00:00
-- url     : https://prove2.me/theorems/736164ce-3ea6-5f12-9d2e-a77c3a99ba6b
-- title:
--   Erdos Girth: exists of deletion
-- statement:
--   **Deletion step.** From a graph on `Fin (2 n)` together with a set `D` of fewer than `n`
--   vertices meeting every short cycle, and with no independent `t`-set, we get a graph on `Fin n`
--   of girth greater than `g` all of whose independent sets have fewer than `t` vertices.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L334-L368
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L334-L368

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth

theorem ErdosGirth.exists_of_deletion (n g t : ℕ) (G : SimpleGraph (Fin (2 * n))) (D : Finset (Fin (2 * n)))
    (hD : 2 * D.card < 2 * n) (hcyc : ∀ u (c : G.Walk u u), c.IsCycle → c.length ≤ g → u ∈ D)
    (hind : ∀ T : Finset (Fin (2 * n)), T.card = t → ¬ G.IsIndepSet (T : Set (Fin (2 * n)))) :
    ∃ H : SimpleGraph (Fin n), (g : ℕ∞) < H.egirth ∧
      ∀ s : Finset (Fin n), H.IsIndepSet (s : Set (Fin n)) → s.card < t := by sorry
