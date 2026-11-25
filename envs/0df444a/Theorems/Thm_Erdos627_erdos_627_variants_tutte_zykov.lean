-- Prove2me | Theorems.Thm_Erdos627_erdos_627_variants_tutte_zykov
-- name    : Erdos627.erdos_627.variants.tutte_zykov
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:07:12.875486+00:00
-- url     : https://prove2.me/theorems/f8565950-24b3-43cb-81e2-204c6a3355a3
-- title:
--   variants: tutte zykov
-- statement:
--   Every integer k ≥ 2 is the chromatic number of a finite graph with clique number two.
--
--   Source: https://github.com/AItoBit/erdos-627-palomar/blob/4a98648f631e1be44b8fcd61f3f7bb48e7388e99/Solution.lean#L19-L22
-- source:
--   https://github.com/AItoBit/erdos-627-palomar/blob/4a98648f631e1be44b8fcd61f3f7bb48e7388e99/Solution.lean#L19-L22

module
public import Definitions.Def_Erdos627
public import Definitions.Def_Erdos627Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Erdos627

theorem Erdos627.erdos_627.variants.tutte_zykov :
    ∀ k : ℕ, 2 ≤ k → ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.cliqueNum = 2 ∧ G.chromaticNumber = (k : ℕ∞) := by sorry
