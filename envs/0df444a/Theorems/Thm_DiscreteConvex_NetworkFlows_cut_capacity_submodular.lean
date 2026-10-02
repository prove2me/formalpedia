-- Prove2me | Theorems.Thm_DiscreteConvex_NetworkFlows_cut_capacity_submodular
-- name    : DiscreteConvex.NetworkFlows.cut_capacity_submodular
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-28T02:17:15.262263+00:00
-- url     : https://prove2.me/theorems/73f383db-e6d7-4a89-8d48-d1a2df4f1642
-- title:
--   Proposition 9.2 -- the cut capacity function is submodular
-- statement:
--   **Proposition 9.2** (p.247). The cut capacity function $\kappa$ is submodular.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247, Proposition 9.2.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247, Proposition 9.2

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_CutCapacity
import Definitions.Def_DiscreteConvex_NetworkFlows_Submodular

namespace DiscreteConvex.NetworkFlows

/-- Proposition 9.2 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.247). The cut capacity
function `κ` is submodular. -/
theorem cut_capacity_submodular {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V]
    (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ) :
    Submodular (CutCapacity tail head cUpper cLower) := by sorry

end DiscreteConvex.NetworkFlows
