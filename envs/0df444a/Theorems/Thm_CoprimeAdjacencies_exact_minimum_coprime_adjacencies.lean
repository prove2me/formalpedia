-- Prove2me | Theorems.Thm_CoprimeAdjacencies_exact_minimum_coprime_adjacencies
-- name    : CoprimeAdjacencies.exact_minimum_coprime_adjacencies
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:54:25.0021+00:00
-- url     : https://prove2.me/theorems/9e34b7e3-d22e-4ebb-9e05-914ed717eb5e
-- title:
--   Coprime Adjacencies: exact minimum coprime adjacencies
-- statement:
--   The exact finite-`n` formula, proved by the constructive path-cover argument.
--
--   Source: https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/Solution.lean#L17-L19
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/Solution.lean#L17-L19

module
public import Definitions.Def_CoprimeAdjacencies
public import Definitions.Def_CoprimeAdjacencies_Solution
set_option autoImplicit true
@[expose] public section
public section
open CoprimeAdjacencies

theorem CoprimeAdjacencies.exact_minimum_coprime_adjacencies (n : ℕ) (hn : 4 ≤ n) :
    P010.h n = P010.target n := by sorry
