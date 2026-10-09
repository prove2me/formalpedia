-- Prove2me | Theorems.Thm_ExpanderBIS_RandomHardCore_lemma_23
-- name    : ExpanderBIS.RandomHardCore.lemma_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:03.069665+00:00
-- url     : https://prove2.me/theorems/2559bf2f-66db-42c2-8328-e394000cdc66
-- title:
--   Lemma 23 — almost every regular bipartite graph has strong small-set expansion
-- statement:
--   There is a degree threshold $\Delta_0$ such that, for each fixed $\Delta\ge\Delta_0$, the proportion of labelled $\Delta$-regular bipartite graphs on two sides of size $m$ that are bipartite $(\sigma,\rho)$-expanders tends to one as $m\to\infty$, where
--
--   $$\sigma=\frac{4\log\Delta}{\Delta},\qquad \rho=\frac{\Delta}{4\log\Delta}-\frac12.$$
--
--   This supplies the expansion event used throughout the polymer reduction. The degree threshold is uniform in the graph size.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 23, Lemma 23

import Mathlib
import Definitions.Def_ExpanderBIS_RandomHardCore_Setting

namespace ExpanderBIS.RandomHardCore

theorem lemma_23 :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ →
      AlmostEvery Δ (fun _ G => IsStdExpander G Δ) := by sorry

end ExpanderBIS.RandomHardCore
