-- Prove2me | Theorems.Thm_FSS23105365_dyadic_lift
-- name    : FSS23105365.dyadic_lift
-- status  : Proved
-- author  : @YY
-- created : 2026-10-09T15:41:02.64352+00:00
-- url     : https://prove2.me/theorems/52d49691-7f65-4ad7-87fe-2beed0c2b2b6
-- title:
--   Lemma E.4 — a transition-dyadic lift
-- statement:
--   For every nonempty finite real-valued Markov chain $M$ such that all finite trajectory probabilities are dyadic, there are a nonempty finite Markov chain $N$ and a state map $\phi$ to the states of $M$. Every initial and transition probability of $N$ is dyadic. For every $n\geq0$ and trajectory $\gamma$ of $M$, summing the probabilities of all $N$ trajectories whose coordinatewise image under $\phi$ is $\gamma$ gives exactly the probability of $\gamma$.
-- source:
--   Jiarui Zhang, Chengwei Liang, Haozhe Jiang, Binhang Yuan, Jingzhao Zhang, Revision Provably Reduces Sequential Computation in Diffusion Language Models, Zenodo preprint, 2026-10-02, https://doi.org/10.5281/zenodo.23105365, Lemma E.4, Eq. (36), printed pp. 34–35.

import Definitions.Def_FSS23105365_FiniteState
set_option autoImplicit false

namespace FSS23105365
theorem dyadic_lift (q : ℕ) (hq : 0 < q) (M : MarkovChain q)
    (hM : PathDyadic M) :
    ∃ r : ℕ, 0 < r ∧ ∃ N : MarkovChain r, ∃ φ : Fin r → Fin q,
      TransitionDyadic N ∧
      ∀ n : ℕ, ∀ γ : Path q n, projectedPathLaw N φ γ = pathLaw M γ := by sorry
end FSS23105365
