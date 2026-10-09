-- Prove2me | Theorems.Thm_ExpanderBIS_Potts_lemma_12
-- name    : ExpanderBIS.Potts.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:20.002657+00:00
-- url     : https://prove2.me/theorems/155c3f71-4bcd-48d1-8cc5-4b9d2f5c7895
-- title:
--   Lemma 12 — strict-majority colorings approximate the Potts partition sum
-- statement:
--   Let $G$ be a nonempty finite $\alpha$-expander, with $\alpha>0$ and $q\ge2$ colors. For inverse temperature $\beta>2\log(eq)/\alpha$, let $Z_G^*(\beta)$ sum the Potts weights of colorings in which some color occupies more than half the vertices. Then
--
--   $$
--   e^{-e^{-n}}Z_G^*(\beta)\le Z_{G,q}(\beta)\le e^{e^{-n}}Z_G^*(\beta),\qquad n=|V(G)|.
--   $$
--
--   This estimates the contribution of colorings with no strict-majority color. It is the first approximation in the reduction to a polymer model.
--
--   **Formalization Note** The vertex set is required to be nonempty: on the empty graph the strict-majority sum vanishes while the Potts partition sum is one. The strict majority is $2|\omega^{-1}(j)|>n$.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 13, Lemma 12

import Mathlib
import Definitions.Def_ExpanderBIS_Potts_Setting

namespace ExpanderBIS.Potts

open Finset

/-- Lemma 12, p. 13. -/
theorem lemma_12 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (α β : ℝ) (q : ℕ)
    (hα : 0 < α) (hq : 2 ≤ q) (hG : IsExpander G α)
    (hβ : 2 * Real.log (Real.exp 1 * (q : ℝ)) / α < β) :
    IsRelApprox (Real.exp (-(Fintype.card V : ℝ)))
      (pottsZstar G q β) (pottsZ G q β) := by sorry

end ExpanderBIS.Potts
