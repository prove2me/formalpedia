-- Prove2me | Theorems.Thm_FSS23105365_conditioned_markov
-- name    : FSS23105365.conditioned_markov
-- status  : Proved
-- author  : @YY
-- created : 2026-10-09T16:02:41.39542+00:00
-- url     : https://prove2.me/theorems/ddda2573-1e95-4b49-8878-5c11be0c8b09
-- title:
--   Theorem E.6 — acceptance-conditioned Markov sampling
-- statement:
--   For every nonempty finite Markov chain $M$, there are natural constants $D,C,k$ depending only on $M$. For every set $F$ of states, every $n\geq0$ with $\Pr[X_n\in F]>0$, and every $0<\epsilon\leq1/2$, a nonuniform circuit samples the complete trajectory conditioned on $X_n\in F$ to total variation error at most $\epsilon$. Its depth is at most $D$, its size is at most $C((n+1)/\epsilon)^k$, and its seed has at most $C(n+\log_2(1/\epsilon))$ fair bits. Every output is a positive-probability trajectory ending in $F$. No positive lower bound on the acceptance probability is assumed. Taking $F=Q$ gives the unconditioned approximate result.
-- source:
--   Jiarui Zhang, Chengwei Liang, Haozhe Jiang, Binhang Yuan, Jingzhao Zhang, Revision Provably Reduces Sequential Computation in Diffusion Language Models, Zenodo preprint, 2026-10-02, https://doi.org/10.5281/zenodo.23105365, Theorem E.6, printed pp. 35–36.

import Definitions.Def_FSS23105365_FiniteState
set_option autoImplicit false

namespace FSS23105365
theorem conditioned_markov (q : ℕ) (hq : 0 < q) (M : MarkovChain q) :
    ∃ D C k : ℕ, ∀ F : Finset (Fin q), ∀ n : ℕ,
      0 < acceptanceProbability M F n →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ S : Circuit (Fin (n + 1) × Fin q),
        S.depth ≤ D ∧
        (S.size : ℝ) ≤ (C : ℝ) * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
        (S.randomBits : ℝ) ≤ (C : ℝ) * ((n : ℝ) + logInv ε) ∧
        SupportPreserving S pathEncode (conditionedPathLaw M F) ∧
        tv (mass S pathEncode) (conditionedPathLaw M F) ≤ ε := by sorry
end FSS23105365
