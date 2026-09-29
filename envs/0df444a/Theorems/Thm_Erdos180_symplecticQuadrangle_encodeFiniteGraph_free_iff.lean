-- Prove2me | Theorems.Thm_Erdos180_symplecticQuadrangle_encodeFiniteGraph_free_iff
-- name    : Erdos180.symplecticQuadrangle_encodeFiniteGraph_free_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:18:37.711908+00:00
-- url     : https://prove2.me/theorems/f75ef1a6-8b69-4ef1-8acf-3e98473a266c
-- title:
--   Encoding does not affect freeness
-- statement:
--   A finite graph embeds into the quadrangle's incidence graph if and only if its canonical
--   encoding does. The encoding is an isomorphism onto a `Fin`-indexed copy, so it changes nothing
--   about subgraph containment; this lemma lets freeness statements be stated for the members of
--   $\mathcal{F}$ exactly as they are stored.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L8086-L8093

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Field.Defs
import Mathlib.Combinatorics.SimpleGraph.Copy

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.symplecticQuadrangle_encodeFiniteGraph_free_iff
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    (encodeFiniteGraph G).graph.Free
        (symplecticQuadrangle K) ↔
      G.Free (symplecticQuadrangle K) := by sorry
