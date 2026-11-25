-- Prove2me | Theorems.Thm_ErdosGirth_exists_girth_indep
-- name    : ErdosGirth.exists_girth_indep
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:29:15.921196+00:00
-- url     : https://prove2.me/theorems/682ff38d-02f6-518f-9f9f-dcabe49f96f6
-- title:
--   Erdos Girth: exists girth indep
-- statement:
--   **Erdős (1959), structural form.** For every `g` and every `ε > 0`, for all sufficiently large
--   `n` there is a graph on `n` vertices with no cycle of length at most `g` in which every independent
--   set has fewer than `ε n` vertices.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirth.lean#L37-L47
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirth.lean#L37-L47

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
public import Definitions.Def_GirthLib_ErdosGirth
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth

theorem ErdosGirth.exists_girth_indep (g : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n), (g : ℕ∞) < G.egirth ∧
      ∀ s : Finset (Fin n), G.IsIndepSet (s : Set (Fin n)) → (s.card : ℝ) < ε * n := by sorry
