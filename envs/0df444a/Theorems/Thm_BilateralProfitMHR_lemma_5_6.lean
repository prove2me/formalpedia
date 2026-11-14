-- Prove2me | Theorems.Thm_BilateralProfitMHR_lemma_5_6
-- name    : BilateralProfitMHR.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:40.377896+00:00
-- url     : https://prove2.me/theorems/bfae04fe-41bb-40d5-a82f-c36ff02aea40
-- title:
--   Lemma 5.6 — convex optimization from trade bits, $O(\sqrt{n\log T}\log^2(2n))$
-- statement:
--   There is a universal constant $C$ with the following property. Let $2\le K\le T$, $\delta\ge1/K$, and let $\mathcal K\subseteq\{0<p<q<1\}$ be nonempty, compact and convex (as returned by Initialize mhr on the clean event). For every $n\ge1$ there is an $n$-query algorithm on $\mathcal K$, chosen from these data only (ConOpt initialized as in Optimize), such that for every pair of independent MHR seller and buyer laws with densities strictly positive on $[0,1]$ and $\delta/2\le\mu\le6\delta$ on $\mathcal K$, when each query $x=(p,q)$ is answered by $Z=H_{N-1}-\log(q-p)$ with $N\sim\mathrm{Geom}(P(p,q))$ (posting $x$ until the first trade, with no limit on the rounds), the query points $x_1,\dots,x_n\in\mathcal K$ satisfy
--   $$\mathbb E\Big[\sum_{\tau=1}^n\big(L(x_\tau)-\min_{x\in\mathcal K}L(x)\big)\Big]=\mathbb E\Big[\sum_{\tau=1}^n\log\frac{\mu^\star_{\mathcal K}}{\mu(x_\tau)}\Big]\le C\sqrt{n\log T}\,\log^2(2n),\tag{33}$$
--   where $L=-\log\mu$ and $\mu^\star_{\mathcal K}=\max_{\mathcal K}\mu$.
--
--   Together with Wald's identity this bounds the regret of the optimization phase of the MHR algorithm.
--
--   Differences from the source:
--   - generalization: "a complete transcript compatible with the clean event $\mathcal E$ on which Initialize mhr triggers and returns $(\delta,\mathcal K)$" → every $2\le K\le T$, $\delta\ge1/K$ and nonempty compact convex $\mathcal K\subseteq\operatorname{int}\mathcal T$ with $\delta/2\le\mu\le6\delta$ on $\mathcal K$; reason: the proof uses only these properties, which every such transcript has (Lemma 5.3 (i)–(ii), (34)); the statement specializes to the source's
--   - reading: "initialize ConOpt as in Optimize for $n$ queries" → there is an $n$-query algorithm on $\mathcal K$ chosen from $\mathcal K$, $n$, $\delta$, $K$, $T$ before the distribution; reason: ConOpt is the algorithm whose existence Corollary 3.1 asserts, initialized with these known data (loss range $[-\log6\delta,\log2/\delta]$, $\psi_2$ bound $4\sqrt{1+\log2K}$)
--   - encoding: "answer each query using the estimator in Equation (32), without a trading-round limit" → each observation has the law of $H_{N-1}-\log(q-p)$ with $N\sim\mathrm{Geom}(P(p,q))$, independent of the past; reason: fresh i.i.d. valuations at a fixed price make the waiting time geometric (35)
--   - encoding: $O(\cdot)$; $\min_{\mathcal K}L$, $\mu^\star_{\mathcal K}$; the expectations → a universal constant $C$; infimum and supremum on $\mathcal K$ (attained); $[0,\infty]$-valued nested integrals; reason: the summands are nonnegative on $\mathcal K$
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Lemma 5.6 and Equation (33), p.35 (PDF 37); Equation (32), p.34 (PDF 36)

import Mathlib
import Definitions.Def_BilateralProfitMHR_Model
import Definitions.Def_BilateralProfitMHR_ConvexBandit
import Definitions.Def_BilateralProfitMHR_LogProfitOracle

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade

/-- **Lemma 5.6 (Convex optimization from trade bits)**, Brüstle, di Gregorio, Fusco, Leonardi
(manuscript, sha256 e91e8127…), p.35 (PDF 37): fix a complete transcript compatible with the
clean event on which Initialize mhr triggers and returns `(δ, 𝒦)`. For any integer `n ≥ 1`,
initialize ConOpt as in Optimize for `n` queries and answer each query using the estimator (32),
without a trading-round limit. Conditional on this transcript, the query points
`x_1, …, x_n ∈ 𝒦` satisfy
`E[∑_τ (L(x_τ) − min_{𝒦} L)] = E[∑_τ log(µ⋆_𝒦/µ(x_τ))] = O(√(n log T) log²(2n))` (33).

**Formalization Note.** The transcript enters only through `2 ≤ K ≤ T`, `δ ≥ 1/K`, and a region
`𝒦` that is nonempty, compact, convex, inside `int 𝒯`, with `δ/2 ≤ µ ≤ 6δ` on `𝒦` (what the clean
event and the trigger give, Lemma 5.3 (i)–(ii) and (34)); the statement holds for every such
data. ConOpt (the algorithm of Corollary 3.1, initialized with `𝒦`, `n`, the loss range
`[−log 6δ, log 2/δ]` and the `ψ₂` bound `4√(1 + log 2K)`) is "an `n`-query algorithm on `𝒦`
chosen from `𝒦`, `n`, `δ`, `K` (and `T`), before the distribution". Each query `x = (p, q)` is
answered by `Z = H_{N−1} − log(q − p)` with `N ∼ Geom(P(p, q))` independent of the past
(`oracleLaw`). `min_𝒦 L` is `sInf (L '' 𝒦)` and `µ⋆_𝒦` is `sSup (µ '' 𝒦)`, both attained.
Expectations are `expectedCumLoss` in `ℝ≥0∞`; `C` is universal. Logarithms are natural. -/
theorem lemma_5_6 :
    ∃ C : ℝ, ∀ T K : ℕ, 2 ≤ K → K ≤ T → ∀ δ : ℝ, 1 / (K : ℝ) ≤ δ →
      ∀ R : Set (ℝ × ℝ), R.Nonempty → IsCompact R → Convex ℝ R → R ⊆ intT →
        ∀ n : ℕ, 1 ≤ n →
          ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
            ∃ A : QueryAlg (ℝ × ℝ) Ω, A.IsOn R ∧
              ∀ E : Environment, UnitSupport E → IsMHR E →
                (∀ x ∈ R, δ / 2 ≤ muP E.prior x ∧ muP E.prior x ≤ 6 * δ) →
                expectedCumLoss A P (fun _ _ _ x => oracleLaw E.prior x)
                    (fun x => ENNReal.ofReal (lossL E.prior x - sInf (lossL E.prior '' R))) n =
                  expectedCumLoss A P (fun _ _ _ x => oracleLaw E.prior x)
                    (fun x => ENNReal.ofReal
                      (Real.log (sSup (muP E.prior '' R) / muP E.prior x))) n ∧
                expectedCumLoss A P (fun _ _ _ x => oracleLaw E.prior x)
                    (fun x => ENNReal.ofReal (lossL E.prior x - sInf (lossL E.prior '' R))) n ≤
                  ENNReal.ofReal (C * Real.sqrt (n * Real.log T) * Real.log (2 * n) ^ 2) := by sorry

end BilateralProfitMHR
