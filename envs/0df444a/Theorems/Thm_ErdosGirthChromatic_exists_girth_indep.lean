-- Prove2me | Theorems.Thm_ErdosGirthChromatic_exists_girth_indep
-- name    : ErdosGirthChromatic.exists_girth_indep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:39:50.786239+00:00
-- url     : https://prove2.me/theorems/07b2d8c3-71aa-4f43-8dca-27e9386e2176
-- title:
--   Erdos Girth Chromatic: exists girth indep
-- statement:
--   **Erdős (1959), structural form.** For every `g` and every `ε > 0`, for all sufficiently large
--   `n` there is a graph on `n` vertices with no cycle of length at most `g` in which every independent
--   set has fewer than `ε n` vertices.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Solution.lean#L39-L42
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Solution.lean#L39-L42

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirth
public import Definitions.Def_Mycielski_Family
public import Definitions.Def_FractionalLib_LarsenProppUllman
public import Definitions.Def_ErdosGirthChromatic_Solution
public import Theorems.Thm_ErdosGirth_exists_girth_indep

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirthChromatic

theorem ErdosGirthChromatic.exists_girth_indep (g : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n), (g : ℕ∞) < G.egirth ∧
      ∀ s : Finset (Fin n), G.IsIndepSet (s : Set (Fin n)) → (s.card : ℝ) < ε * n := by sorry
