-- Prove2me | Theorems.Thm_ExpanderBIS_RandomHardCore_lemma_25
-- name    : ExpanderBIS.RandomHardCore.lemma_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:38:08.279177+00:00
-- url     : https://prove2.me/theorems/2c22af30-b537-45eb-b510-360a9d6f06d7
-- title:
--   Lemma 25 — two polymer partition functions approximate the hard-core partition function
-- statement:
--   There is $\Delta_0$ such that, for $\Delta\ge\Delta_0$ and $\lambda>20\log^2\Delta/\Delta$, every $\Delta$-regular bipartite graph $G$ with the standard expansion property satisfies the following. Let $n=2m$, let $Z_G(\lambda)$ be the hard-core partition function, and set $\widetilde Z_G(\lambda)=(1+\lambda)^m(\Xi^{\mathcal E}(G)+\Xi^{\mathcal O}(G))$. With $\varepsilon_0=(1+\lambda)^{-n/4}$,
--
--   $$e^{-\varepsilon_0}\widetilde Z_G(\lambda)\le Z_G(\lambda)\le e^{\varepsilon_0}\widetilde Z_G(\lambda).$$
--
--   This is the approximation half of the main reduction, at the weaker activity threshold stated by the paper.
--
--   **Formalization Note** The graph has two fixed labelled sides. The right side of the paper's last displayed proof bound names $Z^*_{\mathcal O}$ where the intended lower bound is for $Z_G$.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, pp. 24–25, Lemma 25

import Mathlib
import Definitions.Def_ExpanderBIS_RandomHardCore_Setting

namespace ExpanderBIS.RandomHardCore

theorem lemma_25 :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ →
      ∀ lam : ℝ, 20 * Real.log Δ ^ 2 / Δ < lam →
        ∀ m : ℕ, ∀ G : SimpleGraph (Vertex m),
          G ∈ Gbip m Δ → IsStdExpander G Δ →
            ExpanderBIS.Potts.IsRelApprox ((1 + lam) ^ (-(2 * (m : ℝ)) / 4))
              ((1 + lam) ^ m *
                (sideXi G Δ (evenSide m) lam + sideXi G Δ (oddSide m) lam))
              (hardcoreZ G lam) := by sorry

end ExpanderBIS.RandomHardCore
