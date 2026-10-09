-- Prove2me | Theorems.Thm_ExpanderBIS_Colorings_lemma_23
-- name    : ExpanderBIS.Colorings.lemma_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:34:15.874983+00:00
-- url     : https://prove2.me/theorems/dd5cddfa-10a4-46b3-9736-a7c8d805dae8
-- title:
--   Lemma 23 — for Δ ≥ Δ₀, almost every Δ-regular bipartite graph is a (4 log Δ/Δ, Δ/(4 log Δ) − 1/2)-expander
-- statement:
--   There exists $\Delta_0$ such that for every $\Delta \ge \Delta_0$, almost every $\Delta$-regular bipartite graph is a bipartite
--   $$\Bigl(\frac{4\log\Delta}{\Delta},\ \frac{\Delta}{4\log\Delta} - \frac12\Bigr)\text{-expander}.$$
--   That is, the fraction of graphs $G \in \mathcal G^{\mathrm{bip}}(2m,\Delta)$ in which every set $S$ inside one side with $|S| \le \frac{4\log\Delta}{\Delta}m$ satisfies $|\partial S| \ge \bigl(\frac{\Delta}{4\log\Delta} - \frac12\bigr)|S|$ tends to $1$ as $m \to \infty$.
--
--   This is the only property of the random graph that the proof of Theorem 5 uses; every other statement of the mission is deterministic under this expansion hypothesis.
--
--   **Formalization Note.** The random graph is the uniform labelled graph on two fixed sides of size $m$. The same lemma is posed in the hard-core mission of this series under another namespace, because draft items cannot import one another.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 23, Lemma 23

import Mathlib
import Definitions.Def_ExpanderBIS_Colorings_Setting

open Classical Finset

namespace ExpanderBIS.Colorings

theorem lemma_23 :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ →
      ExpanderBIS.RandomHardCore.AlmostEvery Δ (fun _ G => ExpanderBIS.RandomHardCore.IsStdExpander G Δ) := by sorry

end ExpanderBIS.Colorings
