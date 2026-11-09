-- Prove2me | Theorems.Thm_BudgetedAuctionLearning_Robustness_smoothed_dual_properties
-- name    : BudgetedAuctionLearning.Robustness.smoothed_dual_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:09.928036+00:00
-- url     : https://prove2.me/theorems/d740825c-b90c-4933-8b79-64e2e3ab0c08
-- title:
--   Lemma 5.7 — properties of the smoothed threshold
-- statement:
--   Let $\mu\ge0$, $\rho_L>0$, $E[v_L]>0$ and $\sigma>0$. The average $g^\star_\sigma$ of Eq. (17) satisfies all of:
--
--   1. It is weakly increasing on $[0,\infty)$.
--   2. $-\infty<g^\star(0)\le g^\star_\sigma(\lambda)\le0$ for $\lambda\ge0$.
--   3. If $g^\star(\lambda)=0$ then $g^\star_\sigma(\lambda)=0$.
--   4. For every $\lambda\ge0$, $f(\lambda,g^\star_\sigma(\lambda))\le R^\star+\mu\sigma$.
--   5. For every $\lambda,\varepsilon\ge0$,
--
--   $$0\le g^\star_\sigma(\lambda+\varepsilon)-g^\star_\sigma(\lambda)\le-\frac{\varepsilon}{\sigma}g^\star(\lambda).$$
--
--   These replace the possibly discontinuous $g^\star$ by a Lipschitz function that keeps its properties up to $\mu\sigma$.
--
--   Differences from the source:
--   - generalization: $\mu$ is the optimal multiplier of Lemma 3.3 (which assumes $E[v_L],E[v_O]>0$) → every $\mu\ge 0$, with $R^\star=R^\star(\mu)$; reason: the source's proof uses only that $R^\star$ is the supremum (5) at the given $\mu$, never its optimality; taking the Lemma 3.3 multiplier gives the source's statement
--   - reading: no separate hypothesis on $E[v_L]$ in the statement; $\mu$ comes from Lemma 3.3, which assumes positive expected values → hypothesis $0<E[v_L]$; reason: §5 works with the Lemma 3.3 multiplier and so inherits this; if $E[v_L]=0$ then (5) is infeasible, $R^\star=-\infty$ and $g^\star\equiv-\infty$, so the statement has no meaning. $E[v_O]>0$ is not needed and is not assumed
--   - encoding: real-valued $f$, $R^\star$, $g^\star$ → `EReal` values; `toReal` applied only to $g^\star$ and $P_L$, which are finite here; reason: first-price payments can be $+\infty$; the extended values make that case and the empty cases explicit instead of defaulting to $0$
--   - encoding: fake-value maps in $\mathbb R_{\ge0}^{[0,1]}$ → measurable maps `FakeValue`; reason: the source's expectations need measurability; this is its standing convention
--   - encoding: Lebesgue integral of $g^\star$ in (17) → interval integral of `toReal` of $g^\star$; reason: $g^\star$ is finite and monotone on $[0,\infty)$ under these hypotheses, so the integrand is integrable and the conversion exact
--   - encoding: randomized fake value $\hat V\in\Delta(\mathbb R_{\ge0}^{[0,1]})$ → Markov kernel from $[0,1]$ to $\mathbb R_{\ge0}$; reason: $U_O,P_O,P_L$ depend only on the conditional bid law given $v_O$; every measurable random map yields such a kernel and every kernel on these standard Borel spaces is realized by one
-- source:
--   Fikioris, Tardos, Sivan, STOC 2027 submission #310 (October 2026), Lemma 5.7, printed p. 18 (PDF p. 19); proof printed pp. 18–19 (PDF pp. 19–20)

import Mathlib
import Definitions.Def_BudgetedAuctionLearning_Robustness_DualPotential
open MeasureTheory ProbabilityTheory
open scoped unitInterval NNReal ENNReal

namespace BudgetedAuctionLearning.Robustness

/-- Lemma 5.7, printed p. 18 (PDF p. 19): all five clauses. -/
theorem smoothed_dual_properties (fmt : AuctionFormat) (D : Measure ValuePair) [IsProbabilityMeasure D]
    (ρL μ sig : ℝ) (hρL : 0 < ρL) (hμ : 0 ≤ μ) (hEL : 0 < meanLearnerValue D) (hsig : 0 < sig) :
    MonotoneOn (smoothedThreshold fmt D ρL μ sig) (Set.Ici 0) ∧
    (⊥ < dualThreshold fmt D ρL μ 0 ∧
      ∀ lam, 0 ≤ lam →
        dualThreshold fmt D ρL μ 0 ≤ ((smoothedThreshold fmt D ρL μ sig lam : ℝ) : EReal) ∧
          smoothedThreshold fmt D ρL μ sig lam ≤ 0) ∧
    (∀ lam, 0 ≤ lam → dualThreshold fmt D ρL μ lam = 0 → smoothedThreshold fmt D ρL μ sig lam = 0) ∧
    (∀ lam, 0 ≤ lam →
      dualFunction fmt D ρL μ lam (smoothedThreshold fmt D ρL μ sig lam) ≤
        lagrangianBenchmark fmt D ρL μ + ((μ * sig : ℝ) : EReal)) ∧
    (∀ lam ε, 0 ≤ lam → 0 ≤ ε →
      0 ≤ smoothedThreshold fmt D ρL μ sig (lam + ε) - smoothedThreshold fmt D ρL μ sig lam ∧
        smoothedThreshold fmt D ρL μ sig (lam + ε) - smoothedThreshold fmt D ρL μ sig lam ≤
          -(ε / sig) * (dualThreshold fmt D ρL μ lam).toReal) := by sorry

end BudgetedAuctionLearning.Robustness
