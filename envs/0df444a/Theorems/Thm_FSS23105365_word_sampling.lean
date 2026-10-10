-- Prove2me | Theorems.Thm_FSS23105365_word_sampling
-- name    : FSS23105365.word_sampling
-- status  : Proved
-- author  : @YY
-- created : 2026-10-09T15:56:37.480557+00:00
-- url     : https://prove2.me/theorems/269ee233-6f45-44f7-afc1-7ef170b9ccfb
-- title:
--   Theorem E.2 — support-preserving uniform word sampling
-- statement:
--   For every binary DFA $A$, there are natural constants $D,C,k$, independent of $n$ and $\epsilon$, such that for every nonempty accepted length-$n$ slice and every $0<\epsilon\leq1/2$, there is a nonuniform fair-bit circuit of depth at most $D$ and size at most $C((n+1)/\epsilon)^k$. It uses at most $n+C\log_2(1/\epsilon)$ fair bits. Every seed produces an accepted word, and its output law is within total variation $\epsilon$ of the uniform law on that slice. Using a shared enlarged $C$ for size and randomness is a conventional equivalent choice of constants.
-- source:
--   Jiarui Zhang, Chengwei Liang, Haozhe Jiang, Binhang Yuan, Jingzhao Zhang, Revision Provably Reduces Sequential Computation in Diffusion Language Models, Zenodo preprint, 2026-10-02, https://doi.org/10.5281/zenodo.23105365, Theorem E.2, printed p. 33.

import Definitions.Def_FSS23105365_FiniteState
set_option autoImplicit false

namespace FSS23105365
theorem word_sampling (q : ℕ) (A : BinaryDFA q) :
    ∃ D C k : ℕ, ∀ n : ℕ, (acceptedWords A n).Nonempty →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ S : Circuit (Fin n),
        S.depth ≤ D ∧
        (S.size : ℝ) ≤ (C : ℝ) * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
        (S.randomBits : ℝ) ≤ (n : ℝ) + (C : ℝ) * logInv ε ∧
        SupportPreserving S (fun x : Bits n => x) (wordLaw A) ∧
        tv (mass S (fun x : Bits n => x)) (wordLaw A) ≤ ε := by sorry
end FSS23105365
