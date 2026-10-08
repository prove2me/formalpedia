-- Prove2me | Theorems.Thm_BoydADMM_Constrained_consensus_projection
-- name    : BoydADMM.Constrained.consensus_projection
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:07:39.622636+00:00
-- url     : https://prove2.me/theorems/4114f14b-7106-4bc6-8bb5-f3c4d4730e55
-- title:
--   Projection onto consensus repeats the average
-- statement:
--   Let $N\ge1$ and write $v=(v_1,\ldots,v_N)\in(\mathbb R^n)^N$. The Euclidean projection of $v$ onto the consensus set $\mathcal D=\{(z,\ldots,z):z\in\mathbb R^n\}$ is the constant block vector with value $\bar v=N^{-1}\sum_i v_i$:
--
--   $$\Pi_{\mathcal D}(v)=(\bar v,\ldots,\bar v).$$
--
--   This is the averaging step in the product-space formulation of parallel projections.
--
--   **Formalization Note** The statement uses squared stacked Euclidean distance and includes $N\ge1$ so the mean is defined in the source's sense.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 35, §5.1.2, consensus projection display; https://doi.org/10.1561/2200000016

import Mathlib
import Definitions.Def_BoydADMM_Constrained_Geometry

namespace BoydADMM.Constrained

/-- §5.1.2, p. 35: projection onto the diagonal consensus set repeats the block average. -/
theorem consensus_projection {N n : ℕ} (hN : 0 < N) (v : Blocks N n) :
    IsBlockProjection (consensusSet N n) v (fun _ => avg v) := by sorry

end BoydADMM.Constrained
