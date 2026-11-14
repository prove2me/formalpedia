-- Prove2me | Theorems.Thm_BilateralProfitMHR_claim_5_5
-- name    : BilateralProfitMHR.claim_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:29.78477+00:00
-- url     : https://prove2.me/theorems/1801a3f1-c691-41c1-9c55-4cd89919d7d2
-- title:
--   Claim 5.5 — $\mathbb E[H_{N-1}]=-\log Q$ and $\|H_{N-1}+\log Q\|_{\psi_2}\le4\sqrt{1-\log Q}$ for $N\sim\mathrm{Geom}(Q)$
-- statement:
--   Let $Q\in(0,1]$ and let $N\sim\mathrm{Geom}(Q)$, the number of trials up to and including the first success. With $H_m=\sum_{k=1}^m1/k$ and $H_0=0$,
--   $$\mathbb E[H_{N-1}]=-\log Q,\qquad \|H_{N-1}+\log Q\|_{\psi_2}\le4\sqrt{1-\log Q},$$
--   where $\|\cdot\|_{\psi_2}$ is the subgaussian norm (Definition 5.2).
--
--   Posting a price pair until the first trade therefore gives an unbiased estimate of $-\log P(p,q)$ with subgaussian noise, which is the observation model needed for Corollary 3.1.
--
--   Differences from the source:
--   - encoding: $\mathbb E[H_{N-1}]=-\log Q$ → $H_{N-1}$ is integrable and its integral is $-\log Q$; reason: the expectation is finite (it equals $-\log Q$), and integrability makes the integral the true mean
--   - encoding: $\|\cdot\|_{\psi_2}\le4\sqrt{1-\log Q}$ → the published $[0,\infty]$-valued subgaussian norm is at most $4\sqrt{1-\log Q}$; reason: Definition 5.2's infimum, with value $\infty$ for a non-subgaussian variable; same instances
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Claim 5.5, p.35 (PDF 37); proof App. A.5, pp.60–61 (PDF 62–63)

import Mathlib
import Definitions.Def_BilateralProfitMHR_LogProfitOracle
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm_v2

namespace BilateralProfitMHR

open MeasureTheory

/-- **Claim 5.5 (Estimating a logarithm from a geometric waiting time)**, Brüstle, di Gregorio,
Fusco, Leonardi (manuscript, sha256 e91e8127…), p.35 (PDF 37); proof App. A.5, pp.60–61
(PDF 62–63): let `Q ∈ (0, 1]` and `N ∼ Geom(Q)`. Then `E[H_{N−1}] = −log Q` and
`‖H_{N−1} + log Q‖_{ψ₂} ≤ 4 √(1 − log Q)`.

**Formalization Note.** `Geom(Q)` is `geomLaw Q` on `{1, 2, …}`; `H_m = ∑_{k=1}^m 1/k`,
`H_0 = 0`. The expectation is stated together with the integrability of `H_{N−1}` (so the
Bochner integral is the true mean). `‖·‖_{ψ₂}` is the published `subgaussianNorm` (Definition
5.2), valued in `ℝ≥0∞` and `⊤` for a non-subgaussian variable, so the bound also asserts that
`H_{N−1} + log Q` is subgaussian. Logarithms are natural. -/
theorem claim_5_5 (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1) :
    Integrable (fun N : ℕ => harm (N - 1)) (geomLaw Q) ∧
      ∫ N, harm (N - 1) ∂(geomLaw Q) = -Real.log Q ∧
      HighDimProb.Concentration.subgaussianNorm (geomLaw Q)
          (fun N : ℕ => harm (N - 1) + Real.log Q) ≤
        ENNReal.ofReal (4 * Real.sqrt (1 - Real.log Q)) := by sorry

end BilateralProfitMHR
