-- Prove2me | Theorems.Thm_FSS23105365_exact_markov
-- name    : FSS23105365.exact_markov
-- status  : Proved
-- author  : @YY
-- created : 2026-10-09T15:44:47.330042+00:00
-- url     : https://prove2.me/theorems/e7506cc1-ae1d-4e81-a7bb-829d080c68cb
-- title:
--   Theorem E.5 — exact Markov sampling iff path-dyadic
-- statement:
--   For every nonempty finite Markov chain $M$ with arbitrary nonnegative real transition probabilities and normalized initial and transition laws, the family of complete trajectories $(X_0,\ldots,X_n)$ has exact randomized $\mathrm{AC}^0$ samplers of polynomial size in $n+1$ and depth uniformly bounded independently of $n$ if and only if every finite trajectory probability is dyadic. This includes $n=0$. All random seeds must encode valid trajectories. The condition concerns complete path probabilities, rather than entrywise dyadicity of the original transition matrix.
-- source:
--   Jiarui Zhang, Chengwei Liang, Haozhe Jiang, Binhang Yuan, Jingzhao Zhang, Revision Provably Reduces Sequential Computation in Diffusion Language Models, Zenodo preprint, 2026-10-02, https://doi.org/10.5281/zenodo.23105365, Theorem E.5, printed p. 35.

import Definitions.Def_FSS23105365_FiniteState
set_option autoImplicit false

namespace FSS23105365
theorem exact_markov (q : ℕ) (hq : 0 < q) (M : MarkovChain q) :
    ExactPathAC0 M ↔ PathDyadic M := by sorry
end FSS23105365
