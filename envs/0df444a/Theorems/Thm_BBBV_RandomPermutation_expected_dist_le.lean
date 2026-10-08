-- Prove2me | Theorems.Thm_BBBV_RandomPermutation_expected_dist_le
-- name    : BBBV.RandomPermutation.expected_dist_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:08:20.776802+00:00
-- url     : https://prove2.me/theorems/130648ca-e80b-4ca5-98af-0edf61859c6a
-- title:
--   Proof of Theorem 3.6 — expected distance between consecutive oracle runs
-- statement:
--   Let $T\ge1$ and $T\le 2^{n/3}/100$. Run the same $T$-query algorithm with the fixed permutation oracle $\pi_T$ and with $\pi_{T-1}$, respectively. Averaged over the paper's random transposition chain, the final states satisfy
--
--   $$\mathbb E\bigl[\|\phi_T-\phi'_T\|\bigr]\le\frac{1}{50}.$$
--
--   This quantitative state bound is the immediate input to the final bounded-error argument.
--
--   **Formalization Note** $T\ge1$ makes $\pi_{T-1}$ a genuine preceding oracle. No lower bound on $n$ is needed for this statement; when the query bound forces $T=0$, its hypotheses cannot hold. The constant $1/50$ remains valid with the corrected factor $2$ in Theorem 3.3.
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, p. 11, proof of Theorem 3.6, expected-distance claim and final inequality

import Mathlib
import Definitions.Def_BBBV_RandomPermutation_Chain

namespace BBBV.RandomPermutation

theorem expected_dist_le {n T : ℕ} {W : Type} [Fintype W]
    (M : QueryAlg (BBBV.RandomOracle.Str n) (BBBV.RandomOracle.Str n) W T) (hT1 : 1 ≤ T)
    (hT : (T : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 3) / 100) :
    avg (fun ω : Ω n T =>
      ‖final M (fun _ => ⇑(piChain ω T)) -
        final M (fun _ => ⇑(piChain ω (T - 1)))‖) ≤ 1 / 50 := by sorry

end BBBV.RandomPermutation
