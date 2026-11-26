-- Prove2me | Theorems.Thm_FD1D_uniform_map_lawInvariant
-- name    : FD1D.uniform_map_lawInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:00.947912+00:00
-- url     : https://prove2.me/theorems/e83e4f7c-2ad1-5512-9c03-2f8e3e7afe56
-- title:
--   FD1 D: uniform map law Invariant
-- statement:
--   A uniform pushforward is invariant under any compatible permutations of
--   its source and target.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L117-L132
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Initialization.lean#L117-L132

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Initialization
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.uniform_map_lawInvariant
    {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [DecidableEq B]
    (f : A → B) (ea : Equiv.Perm A) (eb : Equiv.Perm B)
    (h : ∀ a, f (ea a) = eb (f a)) :
    FiniteKernel.LawInvariant
      ((FiniteLaw.uniform : FiniteLaw A).map f) eb := by sorry
