-- Prove2me | Theorems.Thm_DetPermanentApprox_Main_lemma_2_3
-- name    : DetPermanentApprox.Main.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:29.522265+00:00
-- url     : https://prove2.me/theorems/429a7e92-8b8b-4f10-82a4-b82eb513a667
-- title:
--   Lemma 2.3 — Attainment and exact entropy duality
-- statement:
--   Let $n\ge1$ and let $A\ge0$ have positive permanent and every positive support edge in a perfect matching, as assumed at the start of Section 2. For $0<t<1$, the field objective $\Phi_{A,t}$ attains its minimum. Every minimizer $\theta_t$ has its Gibbs law in $V_t$, and
--
--   $$F_A(t)=\Phi_{A,t}(\theta_t)=\min_\theta\Phi_{A,t}(\theta).$$
--
--   Here $V_t$ consists of all finite laws on all support matchings that cover each vertex with probability $t$. This identifies the prescribed-marginal entropy optimum with an attained field minimum.
--
--   Differences from the source:
--   - encoding: finite labelled matrix, graph, and coordinate sets → Fin n or arbitrary finite types with explicit row and column copies; reason: finite enumerations and reindexing preserve every source instance
--   - encoding: an attained minimum and equality to its value → existence of a globally minimizing field and the equality at every globally minimizing field; reason: the explicit minimizer predicate expresses attainment without a default-valued real infimum
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Lemma 2.3, p. 8 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Matchings

namespace DetPermanentApprox.Main

theorem lemma_2_3 {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hp : 0 < A.permanent) (hs : TotalSupport A)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (∃ θ : Vertex n → ℝ, IsMinimizer (Phi A t) θ) ∧
    (∀ θ : Vertex n → ℝ, IsMinimizer (Phi A t) θ →
      gibbs (supportGraph A) (fieldWeights (supportGraph A) (supportWeights A) θ) ∈
        matchingLaws (supportGraph A) t ∧ F A t = Phi A t θ) := by sorry

end DetPermanentApprox.Main
