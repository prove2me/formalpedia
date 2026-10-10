-- Prove2me | Theorems.Thm_FSS23105365_pair_sampling
-- name    : FSS23105365.pair_sampling
-- status  : Proved
-- author  : @YY
-- created : 2026-10-09T15:42:24.855998+00:00
-- url     : https://prove2.me/theorems/13a34d3a-4d78-4ce8-ab15-c7f24c17cd4e
-- title:
--   Theorem E.1 — exact regular-language pair sampling
-- statement:
--   For every binary DFA $A$ with $q$ states, there are natural constants $D,C,k$ such that for every $n\geq0$, a Boolean circuit supplied with exactly $n$ fair bits outputs $(X,A(X))$ exactly, where $X$ is uniform on $\{0,1\}^n$. Its depth is at most $D$ and its size is at most $C(n+1)^k$. The extra output bit is the accepting-state indicator; acceptance membership need not be in $\mathrm{AC}^0$.
-- source:
--   Jiarui Zhang, Chengwei Liang, Haozhe Jiang, Binhang Yuan, Jingzhao Zhang, Revision Provably Reduces Sequential Computation in Diffusion Language Models, Zenodo preprint, 2026-10-02, https://doi.org/10.5281/zenodo.23105365, Theorem E.1, printed p. 33; seed bound in Appendix E.1 and Proposition 3.2.

import Definitions.Def_FSS23105365_FiniteState
set_option autoImplicit false

namespace FSS23105365
theorem pair_sampling (q : ℕ) (A : BinaryDFA q) :
    ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Option (Fin n)),
      S.randomBits = n ∧ S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
      ExactLaw S pairOutcomeEncode (pairLaw A) := by sorry
end FSS23105365
