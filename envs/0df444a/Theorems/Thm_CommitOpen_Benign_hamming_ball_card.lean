-- Prove2me | Theorems.Thm_CommitOpen_Benign_hamming_ball_card
-- name    : CommitOpen.Benign.hamming_ball_card
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:50.179734+00:00
-- url     : https://prove2.me/theorems/1516333e-dcb4-4490-a372-0f918556cbb6
-- title:
--   p. 11 — the Hamming ball of radius μn in {0,1}^n has at most 2^{h(μ)n} points for 0 ≤ μ ≤ ½
-- statement:
--   For every $n$, every $\hat y\in\{0,1\}^n$ and every $\mu$ with $0\le\mu\le\tfrac12$,
--   $$\big|\{y\in\{0,1\}^n: d_H(y,\hat y)\le\mu n\}\big|\le 2^{h(\mu)n},$$
--   where $h(\mu)=-(\mu\log_2\mu+(1-\mu)\log_2(1-\mu))$ is the binary entropy.
--
--   This counts the strings compatible with an error rate of at most $\mu$, and turns Lemma 2.3's $\log|J|$ into the $h(err+\varepsilon)n$ of Corollary 4.4.
--
--   **Formalization Note.** $\mu$ is real. The bound follows from the Proved platform theorem `choose_sum_le_exp_mul_binEntropy` (integer radius, nats) together with monotonicity of $h$ on $[0,\tfrac12]$; it is not the same statement.
-- source:
--   Damgård, Fehr, Lunemann, Salvail & Schaffner, Improving the Security of Quantum Protocols via Commit-and-Open, arXiv:0902.3918v4, p. 11, paragraph before Corollary 4.4

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace CommitOpen.Benign

theorem hamming_ball_card (n : ℕ) (yhat : Fin n → Bool) (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1 / 2) :
    ((Finset.univ.filter fun y : Fin n → Bool =>
        (hammingOn Finset.univ y yhat : ℝ) ≤ μ * n).card : ℝ) ≤
      (2 : ℝ) ^ (binEntropy2 μ * n) := by sorry

end CommitOpen.Benign
