-- Prove2me | Theorems.Thm_ExpanderBIS_RandomHardCore_theorem_2_reduction
-- name    : ExpanderBIS.RandomHardCore.theorem_2_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:33:40.802398+00:00
-- url     : https://prove2.me/theorems/8cec130d-1771-4038-a818-633cb204293d
-- title:
--   Theorem 2 core — almost-every-graph polymer reduction and KP bound
-- statement:
--   There is a degree threshold $\Delta_0$ such that, for each fixed $\Delta\ge\Delta_0$, the fraction of labelled $\Delta$-regular bipartite graphs with the following property tends to one as the side size $m$ grows. For every $\lambda>50\log^2\Delta/\Delta$, put $n=2m$, $\varepsilon_0=(1+\lambda)^{-n/4}$, and $\widehat Z_G=(1+\lambda)^m(\Xi^{\mathcal E}(G)+\Xi^{\mathcal O}(G))$. Then both conclusions hold:
--
--   1. The hard-core partition function obeys
--
--      $$e^{-\varepsilon_0}\widehat Z_G\le Z_G(\lambda)\le e^{\varepsilon_0}\widehat Z_G.$$
--
--   2. For either polymer family and every polymer $\gamma$ in it, with $g(\eta)=|\eta|\Delta\log(1+\lambda)/(10\log\Delta)$,
--
--      $$\sum_{\eta\text{ incompatible with }\gamma}w_\eta e^{|\eta|+g(\eta)}\le|\gamma|.$$
--
--   These are the deterministic partition-function and convergence claims underlying the paper's algorithmic Theorem 2.
--
--   **Formalization Note** All activities above the threshold are quantified inside one almost-every graph event. The graph model has fixed labelled sides. The FPTAS, sampler, and running time are outside the statement.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 3, Theorem 2 and Remark 1; pp. 23–26, §§4.4–4.5; p. 8, condition (1)

import Mathlib
import Definitions.Def_ExpanderBIS_RandomHardCore_Setting

open Classical

namespace ExpanderBIS.RandomHardCore

theorem theorem_2_reduction :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ →
      AlmostEvery Δ (fun m G =>
        ∀ lam : ℝ, 50 * Real.log Δ ^ 2 / Δ < lam →
          ExpanderBIS.Potts.IsRelApprox ((1 + lam) ^ (-(2 * (m : ℝ)) / 4))
            ((1 + lam) ^ m *
              (sideXi G Δ (evenSide m) lam + sideXi G Δ (oddSide m) lam))
            (hardcoreZ G lam) ∧
          ∀ side ∈ ({oddSide m, evenSide m} : Finset (Finset (Vertex m))),
            ∀ γ ∈ tinyPolymers G Δ side,
              (∑ γ' ∈ (tinyPolymers G Δ side).filter
                (fun γ' => ¬ Compat2 G γ' γ),
                  hcWeight G lam γ' *
                    Real.exp ((γ'.card : ℝ) + decay Δ lam γ')) ≤
                (γ.card : ℝ)) := by sorry

end ExpanderBIS.RandomHardCore
