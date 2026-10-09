-- Prove2me | Theorems.Thm_ExpanderBIS_RandomHardCore_kp_vertex_sum
-- name    : ExpanderBIS.RandomHardCore.kp_vertex_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:33:47.060976+00:00
-- url     : https://prove2.me/theorems/c6463878-e14e-4942-8ad3-a755fc88e81d
-- title:
--   §4.5 — per-vertex polymer sum is at most 1/Δ²
-- statement:
--   There is $\Delta_0$ such that, for $\Delta\ge\Delta_0$ and $\lambda\ge50\log^2\Delta/\Delta$, each standard-expanding $\Delta$-regular bipartite graph has the following bound for either side and every vertex $v$. If $\mathcal C$ is that side's tiny-polymer family and $g(\gamma)=|\gamma|\Delta\log(1+\lambda)/(10\log\Delta)$, then
--
--   $$\sum_{\gamma\in\mathcal C:\,v\in\gamma}w_\gamma e^{|\gamma|+g(\gamma)}\le\frac1{\Delta^2}.$$
--
--   Summing this local bound near a polymer gives the KP inequality in the main goal. The vertex may lie on either side; its sum is zero when it belongs to no polymer of the selected side.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, pp. 25–26, §4.5, displayed per-vertex sum and final estimate

import Mathlib
import Definitions.Def_ExpanderBIS_RandomHardCore_Setting

namespace ExpanderBIS.RandomHardCore

theorem kp_vertex_sum :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ →
      ∀ lam : ℝ, 50 * Real.log Δ ^ 2 / Δ ≤ lam →
        ∀ m : ℕ, ∀ G : SimpleGraph (Vertex m),
          G ∈ Gbip m Δ → IsStdExpander G Δ →
            ∀ side ∈ ({oddSide m, evenSide m} : Finset (Finset (Vertex m))),
              ∀ v : Vertex m,
                (∑ γ ∈ (tinyPolymers G Δ side).filter (fun γ => v ∈ γ),
                  hcWeight G lam γ * Real.exp ((γ.card : ℝ) + decay Δ lam γ)) ≤
                    1 / (Δ : ℝ) ^ 2 := by sorry

end ExpanderBIS.RandomHardCore
