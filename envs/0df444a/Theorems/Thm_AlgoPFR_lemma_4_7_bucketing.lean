-- Prove2me | Theorems.Thm_AlgoPFR_lemma_4_7_bucketing
-- name    : AlgoPFR.lemma_4_7_bucketing
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:35.679743+00:00
-- url     : https://prove2.me/theorems/a45f2327-5a1b-4ab5-8c4d-fe30ee74f52c
-- title:
--   Lemma 4.7 with Claims 4.8–4.9 — bucketing restores constant slack at $\log(3\Delta+3)$ bits
-- statement:
--   Given algorithmic access to $X$ with envelope $M_X$, let $J=\lfloor\log N_X\rfloor$, where $N_X$ is the first success of independent runs of $\mathrm{Coin}_X(x)$ after $x\sim X$, and let $\pi_j=\Pr[J=j]$. Then
--   $$I[X:J]\le\log(3\Delta[X]+3),\qquad\mathbb E_{j\sim J}\,\Delta[X_j]<8,$$
--   and for every $j$ with $\pi_j>0$, Algorithm 1 constructs algorithmic access to $X_j=(X\mid J=j)$ with envelope $M_X/(2^j\pi_j)$. One trial of $\mathrm{Sample}_{X_j}$ is accepted with probability $\pi_j$ and makes $2^{j+1}$ parent calls, the expected number of trials is $1/\pi_j$, and one call to $\mathrm{Coin}_{X_j}$ makes $2^{j+1}$ parent coin calls.
--
--   Bucketing is what stops slack from accumulating along a trajectory.
--
--   Differences from the source:
--
--   - generalization: I[X : J] = O(log Δ[X]), E Δ[X_j] = O(1), expected parent calls O(2^(j+1) / Pr[J = j]), coin at most 2^(j+1) parent coins → the explicit log(3Δ[X] + 3) and 8 of Claim 4.9, exactly 2^(j+1) calls per trial with expected trials 1 / π_j, and exactly 2^(j+1) coins; reason: explicit values are the source's own Claims 4.8–4.9 and imply the O(·) forms, reading O(log Δ) as O(log(Δ + 2)) per p.13
--   - reading: "algorithmic access" of Definition 4.1, including expected poly(n, K) time → the sampler law, the coin rate and the envelope, with call counts in place of time; reason: the expected trial count 1 / π_j is not polynomial for rare labels
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Lemma 4.7, p.24, with Claim 4.8, p.25, and Claim 4.9, p.26

import Mathlib
import Definitions.Def_AlgoPFR_Protocols

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

/-- **Lemma 4.7, with the explicit constants of Claims 4.8–4.9.** Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), pp.24–26: given algorithmic
access to `X`, the label `J = ⌊log N_X⌋` of Algorithm 1 satisfies `I[X : J] ≤ log (3Δ[X] + 3)`, and
Algorithm 1 constructs access to `X_j := (X | J = j)` with envelope `M_X / (2^j Pr[J = j])` and
`E_{j∼J} Δ[X_j] < 8`. The sampler `Sample_{X_j}` is exact, one trial accepts with probability
`π_j = Pr[J = j]`, its expected number of trials is `1 / π_j`, one trial uses `2^(j+1)` parent calls, and
one call to `Coin_{X_j}` uses `2^(j+1)` parent coins.

**Formalization Note.** Lemma 4.7's `O(log Δ[X])` is read as `O(log(Δ[X] + 2))`, the convention of
p.13, and Claim 4.9's explicit bound is that. The `O(1)` for the expected slack is Claim 4.9's `8`.
The `O(2^(j+1) / Pr[J = j])` expected parent calls are the product of two exact facts: `2^(j+1)` calls
per trial and `1 / π_j` expected trials. -/
theorem lemma_4_7_bucketing {n : ℕ} (X : Oracle n) (M : ℝ) (hX : IsAccess X M) :
    labelInfo (bucketJoint X) ≤ Real.logb 2 (3 * slack X M + 3) ∧
      expect (bucketLabel X) (fun j => slack (bucketOracle X j) (bucketEnv X M j)) <
        ENNReal.ofReal 8 ∧
      ∀ j, 0 < bucketProb X j →
        (bucketOracle X j).sample = labelFiber (bucketJoint X) j ∧
          IsAccess (bucketOracle X j) (bucketEnv X M j) ∧
          ((bucketTrial X j).law none).toReal = 1 - bucketProb X j ∧
          expectedTrials (bucketTrial X j).law = ENNReal.ofReal (1 / bucketProb X j) ∧
          (bucketTrial X j).UsesCalls (2 ^ (j + 1)) ∧
          ∀ x, (bucketCoinProc X j x).UsesCalls (2 ^ (j + 1)) := by sorry

end AlgoPFR
