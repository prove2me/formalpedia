-- Prove2me | Theorems.Thm_BBBV_RandomPermutation_expected_queryMag_le
-- name    : BBBV.RandomPermutation.expected_queryMag_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:08:26.427976+00:00
-- url     : https://prove2.me/theorems/5268f459-256a-499b-8227-96b297c88ac3
-- title:
--   Proof of Theorem 3.6 — expected query magnitude of a later sampled string
-- statement:
--   In the hybrid computation, let $\psi_i$ be the state before query step $i$. If $i\le j\le T+1$, then the string $x_j$ sampled by the chain has expected query magnitude at most the reciprocal of the number of length-$n$ binary strings:
--
--   $$\mathbb E[q_{x_j}(\psi_i)]\le 2^{-n}.$$
--
--   This bound applies to the random string $x_j$, including $j=i$, and is the independence estimate needed for the hybrid comparison.
--
--   **Formalization Note** Expectation is a finite average over the explicit chain sample space. At $i=0$, the initial state is fixed and $x_0$ is uniform.
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, p. 11, proof of Theorem 3.6, paragraph beginning 'We claim'

import Mathlib
import Definitions.Def_BBBV_RandomPermutation_Chain

namespace BBBV.RandomPermutation

theorem expected_queryMag_le {n T : ℕ} {W : Type} [Fintype W]
    (M : QueryAlg (BBBV.RandomOracle.Str n) (BBBV.RandomOracle.Str n) W T) (i : Fin T) (j : ℕ)
    (hij : (i : ℕ) ≤ j) (hj : j ≤ T + 1) :
    avg (fun ω : Ω n T => queryMag (x ω j) (state M (hybrid ω) i)) ≤
      1 / (2 : ℝ) ^ n := by sorry

end BBBV.RandomPermutation
