-- Prove2me | Theorems.Thm_Csg_MatrixGame_mem_stdSimplex_comp
-- name    : Csg.MatrixGame.mem_stdSimplex_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:04:34.512893+00:00
-- url     : https://prove2.me/theorems/b437670e-39be-4a8f-8b92-dc18df7fd23b
-- title:
--   Matrix Game: mem std Simplex comp
-- statement:
--   The other direction of `mem_stdSimplex_comp_symm`: pushing a strategy on `I` forward along `e`
--       lands back in `I'`'s own simplex. Needed below to turn `G.optimalRow` (a strategy on `I`) into
--       a candidate strategy on `I'` in the first place. Same unused instances, and the same `omit`,
--       as `mem_stdSimplex_comp_symm`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L506-L509
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L506-L509

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
variable {I' : Type*} [Fintype I'] [Nonempty I'] [DecidableEq I']
omit [Nonempty I] [DecidableEq I] [Nonempty I'] [DecidableEq I']

theorem Csg.MatrixGame.mem_stdSimplex_comp (e : I' ≃ I) {x : I → ℝ} (hx : x ∈ stdSimplex ℝ I) :
    x ∘ ⇑e ∈ stdSimplex ℝ I' := by sorry
