-- Prove2me | Theorems.Thm_FSS23105365_exact_markov_seed
-- name    : FSS23105365.exact_markov_seed
-- status  : Proved
-- author  : @YY
-- created : 2026-10-09T15:47:33.851611+00:00
-- url     : https://prove2.me/theorems/298bb3bd-6bbe-45a1-8cec-94702369581e
-- title:
--   Theorem E.5 — linear fair-bit budget
-- statement:
--   For every nonempty finite path-dyadic Markov chain $M$, there are natural constants $D,C,k$ such that for every $n\geq0$ its complete trajectory law has an exact sampler of depth at most $D$, size at most $C(n+1)^k$ and at most $C(n+1)$ independent fair input bits. The constants depend only on the fixed chain. This records the seed bound stated in Appendix E.1 and obtained by the sufficiency construction for Theorem E.5.
-- source:
--   Jiarui Zhang, Chengwei Liang, Haozhe Jiang, Binhang Yuan, Jingzhao Zhang, Revision Provably Reduces Sequential Computation in Diffusion Language Models, Zenodo preprint, 2026-10-02, https://doi.org/10.5281/zenodo.23105365, Appendix E.1 third bullet, printed p. 33; Theorem E.5 proof, printed p. 35.

import Definitions.Def_FSS23105365_FiniteState
set_option autoImplicit false

namespace FSS23105365
theorem exact_markov_seed (q : ℕ) (hq : 0 < q) (M : MarkovChain q)
    (hM : PathDyadic M) :
    ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Fin (n + 1) × Fin q),
      S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
      S.randomBits ≤ C * (n + 1) ∧ ExactLaw S pathEncode (pathLaw M) := by sorry
end FSS23105365
