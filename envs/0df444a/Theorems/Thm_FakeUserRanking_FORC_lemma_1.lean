-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_lemma_1
-- name    : FakeUserRanking.FORC.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:55.540494+00:00
-- url     : https://prove2.me/theorems/1263e81c-5063-4759-a707-a523a09ba1f1
-- title:
--   Lemma 1, p. 20 — regret is at most F plus the gap-weighted expected number of real examinations of misplaced products
-- statement:
--   **Lemma 1 (Decomposing Regret).** Consider the cascade model with click probabilities $\mu_1>\mu_2>\dots>\mu_n$ in $[0,1]$ (condition (1)) and exit probabilities $q_j\in[0,1]$, a fake-user policy $\mathbf P$ with fakeness budget $F$, and any randomized ranking algorithm $(\pi_t)_{t=1}^T$ that sees only its own past (observations and internal randomness). Then the regret against the optimal ranking $\pi^\star(i)=i$ satisfies
--   $$\mathbb E\Big[\sum_{t=1}^T\mathcal C_{r,t}(\pi^\star)\Big]-\mathbb E\Big[\sum_{t=1}^T\mathcal C_{r,t}(\pi_t)\Big]\le F+\sum_{t=1}^T\sum_{j=1}^n\sum_{i=j+1}^n\Delta_{j,i}\,\mathbb E\big[\mathbb I(\mathcal A_{r,t}(\pi_t(j)=i))\big]\qquad(7),$$
--   where $\mathcal A_{r,t}(\pi_t(j)=i)$ is the event that product $i$ is at position $j$ in round $t$, the customer of round $t$ is real, and she does not exit before position $j$; both runs face the same policy $\mathbf P$.
--
--   The lemma reduces regret to pairwise misplacements: each examination by a real customer of a worse product $i$ placed at the position $j<i$ costs at most the gap $\Delta_{j,i}$, and fake users cost at most $F$ in total. It is the first step of the proofs of Theorems 2 and 3.
--
--   **Formalization Note.** An algorithm is an `Alg n L`: in each round it draws an internal label with weights `w h ·` (nonnegative, summing to 1) that may depend on its past `h` (labels and observations), and displays the ranking `rank h ℓ`. Every randomized algorithm induces the same law of the history as one of these (take the ranking itself as the label). Products and positions are 0-based; `Finset.Ioi j` is $\{i: i>j\}$. Expectations are finite sums over trajectories; $\mathbb E[\mathbb I(\cdot)]$ is `prob`.
--
--   Differences from the source:
--   - encoding: products, positions, levels and rounds indexed from 1; paper level ℓ; ℓ ≥ ℓ⋆ = ⌈log₂F⌉ → Fin n, Fin L, Fin T, all 0-based; Lean level k is paper level ℓ = k + 1; ℓ ≥ ⌈log₂F⌉ is written F ≤ 2^(k+1); reason: Lean convention; same instances (F ≤ 2^ℓ is exactly ℓ ≥ ⌈log₂F⌉, and holds for every level when F = 0)
--   - encoding: expectations and probabilities over the random history H_T → finite sums over trajectories Fin T → Step, weighted by the product of the level weights, the policy's PMF and the real customer's cascade law; reason: every space of the model is finite, so this is the law of the history exactly
--   - encoding: an arbitrary randomized algorithm (π_t : H^o_{t−1} → Π) → Alg n L: per round a label drawn with weights depending on the algorithm's own past (nonnegative, summing to 1), and a ranking that is a function of that past and the label; reason: every randomized algorithm has a behavioural representation with the same history law (label = ranking, L = n!), and every Alg is such an algorithm
--   - encoding: E_{H_t(π_t)}[I(A_{r,t}(π_t(j) = i))] over the t-round history → the probability of the event under the T-round run; reason: the event depends only on the first t rounds and the later rounds' weights sum to 1
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 20, Lemma 1, (7); proof App. C.1, pp. 46–48

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model

namespace FakeUserRanking.FORC

/-- Lemma 1 (Decomposing Regret), p. 20. -/
theorem lemma_1 {n L : ℕ} (T F : ℕ) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (hw_sum : ∀ h, ∑ k, A.w h k = 1)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (P : Adversary n) (hP : WithinBudget F P) :
    regret inst P A T ≤ (F : ℝ) + ∑ t : Fin T, ∑ j : Fin n, ∑ i ∈ Finset.Ioi j,
      gap inst j i * prob inst P A T (fun τ => feedbackEvent A τ t j i) := by sorry

end FakeUserRanking.FORC
