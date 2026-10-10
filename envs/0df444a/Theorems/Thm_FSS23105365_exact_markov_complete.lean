-- Prove2me | Theorems.Thm_FSS23105365_exact_markov_complete
-- name    : FSS23105365.exact_markov_complete
-- status  : Proved
-- author  : @YY
-- created : 2026-10-09T16:07:41.794987+00:00
-- url     : https://prove2.me/theorems/21f9b077-546b-4732-a269-7b5d76868d7c
-- title:
--   Theorem E.5 — exact Markov criterion and linear seed bound
-- statement:
--   For every finite Markov chain $M$ with a nonempty state set, arbitrary nonnegative real initial and transition weights, and normalized probability laws, exact sampling of every complete trajectory law by polynomial-size constant-depth circuits supplied with finitely many fair bits is possible if and only if every finite path probability is dyadic. Length-zero paths are included, so initial probabilities are part of this condition.
--
--   Whenever this condition holds, there exist natural constants $D,C,k$ depending only on $M$, such that at every length $n\ge0$ an exact sampler has depth at most $D$, size at most $C(n+1)^k$ and at most $C(n+1)$ fair bits. Exactness requires every output to encode a trajectory and the probability of each full trajectory to match its Markov probability.
--
--   This statement groups the equivalence in Theorem E.5 together with its linear seed guarantee, stated in the motivation of Appendix E and established by its sufficiency construction. Both components are required for this milestone.
-- source:
--   Jiarui Zhang, Chengwei Liang, Haozhe Jiang, Binhang Yuan, Jingzhao Zhang, Revision Provably Reduces Sequential Computation in Diffusion Language Models, Zenodo preprint, 2026-10-02, https://doi.org/10.5281/zenodo.23105365, Theorem E.5, printed p. 35. Appendix E.1 third bullet and the sufficiency construction, for the linear seed guarantee.

import Definitions.Def_FSS23105365_FiniteState
set_option autoImplicit false
open FSS23105365

theorem FSS23105365.exact_markov_complete :
    (∀ (q : ℕ), 0 < q → ∀ (M : MarkovChain q), ExactPathAC0 M ↔ PathDyadic M) ∧
    (∀ (q : ℕ), 0 < q → ∀ (M : MarkovChain q), PathDyadic M →
      ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Fin (n + 1) × Fin q),
        S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
        S.randomBits ≤ C * (n + 1) ∧ ExactLaw S pathEncode (pathLaw M)) := by sorry
