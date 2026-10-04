-- Prove2me | Theorems.Thm_DiscreteConvex_AlgorithmsB_central_part_nonempty
-- name    : DiscreteConvex.AlgorithmsB.central_part_nonempty
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-28T04:10:38.12599+00:00
-- url     : https://prove2.me/theorems/6545db76-f1c1-4987-8ba0-a24a6dd6ad09
-- title:
--   Proposition 10.6 -- central_part_nonempty
-- statement:
--   **Proposition 10.6** (p.285). $B^\circ
--   e\emptyset$ if $B$ is a bounded nonempty M-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.285, Proposition 10.6.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.285, Proposition 10.6

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_AlgorithmsB_BCirc

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.6 (p.285). `B° ≠ ∅` if `B` is a bounded nonempty M-convex set. -/
theorem central_part_nonempty (B : Set (V → ℤ)) (hB : ExchangeAxiomB B) (hBne : B.Nonempty)
    (hBbdd : ∃ N : ℤ, ∀ y ∈ B, ∀ v, -N ≤ y v ∧ y v ≤ N) :
    (BCirc B).Nonempty := by sorry

end DiscreteConvex.AlgorithmsB
