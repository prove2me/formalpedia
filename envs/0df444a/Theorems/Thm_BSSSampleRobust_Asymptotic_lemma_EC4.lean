-- Prove2me | Theorems.Thm_BSSSampleRobust_Asymptotic_lemma_EC4
-- name    : BSSSampleRobust.Asymptotic.lemma_EC4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T22:27:30.563511+00:00
-- url     : https://prove2.me/theorems/24da081a-eb1f-4ba5-84aa-3b1a68eb69a1
-- title:
--   Lemma EC.4 — Nonnegative support restriction
-- statement:
--   Fix $d\ge1$, an $\ell_p$ norm, $\Xi\subseteq\mathbb R^d$, $Z\subseteq\Xi$, and $N\ge1$ sample points $\hat\xi^1,\ldots,\hat\xi^N\in Z$. Let $g:\Xi\to\mathbb R$ be measurable for the induced Borel sigma algebra and nonnegative on $Z$. Write $\mathcal P(A)$ for probability laws with mass one on $A$, $\widehat P_N$ for the empirical law, and $W_1$ for the transport distance. For every $\theta\ge0$,
--   $$\sup_{Q\in\mathcal P(\Xi):W_1(Q,\widehat P_N)\le\theta} E_Q[g(\xi)I\{\xi\in Z\}]
--   =\sup_{Q\in\mathcal P(Z):W_1(Q,\widehat P_N)\le\theta}E_Q[g(\xi)].$$
--   No sign condition is imposed outside $Z$. This equality is the support restriction used in the uniform inequality.
--
--   Differences from the source:
--   - encoding: finite-dimensional real spaces with any fixed lp norm, 1 ≤ p ≤ ∞ → PiLp over finite coordinates, Borel sigma algebras, and Fact (1 ≤ p); reason: coordinate relabeling preserves every allowed norm and every source instance; the ambient dimension is positive
--   - encoding: extended-real expectation and extrema with infinity minus infinity equal to positive infinity → EReal extrema and the referenced positive-part-first expectation, applied on the completed measure; reason: infeasibility gives positive infinity and unbounded extrema remain infinite; no integrability hypothesis is added
--   - reading: expectations of local suprema and indicators, with page 6 defining set probability as indicator expectation but not specifying completion → completed lower-integral expectations; concentration and retained-set probabilities are expectations of indicators; reason: this preserves the explicit indicator identity without imposing measurability, closedness, continuity, or boundedness; on completed-measurable sets it is the ordinary probability
--   - encoding: samples indexed 1 through N, N positive, under the infinite iid product law → samples indexed by Fin N, drawn from the coordinates 0 through N-1 of Measure.infinitePi on natural numbers; reason: a shift of labels gives the same iid data; finite-sample assertions require N ≥ 1 and asymptotic assertions ignore N = 0
--   - encoding: g is defined on Xi → g is a measurable subtype function, extended by zero outside Xi when integrating ambient laws; reason: this supplies an ambient integrand without imposing global measurability on that extension
-- source:
--   Bertsimas, Shtern and Sturt (2023), A Data-Driven Approach to Multistage Stochastic Linear Optimization, Management Science, https://doi.org/10.1287/mnsc.2022.4352; published basis, supplied manuscript/e-companion artifact; Lemma EC.4, PDF page 62, printed page ec20

import Mathlib
import Definitions.Def_BSSSampleRobust_Asymptotic_Sampling

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BSSSampleRobust.Asymptotic

theorem lemma_EC4 (p : ℝ≥0∞) [Fact (1 ≤ p)] (d : ℕ) (hd : 0 < d)
    (Ξ Z : Set (Vec p (Fin d))) (hZ : Z ⊆ Ξ)
    (N : ℕ) (hN : 1 ≤ N) (data : Fin N → Vec p (Fin d))
    (hdata : ∀ j, data j ∈ Z) (g : Ξ → ℝ) (hg : Measurable g)
    (hnonneg : ∀ z : Ξ, z.val ∈ Z → 0 ≤ g z) (θ : ℝ) (hθ : 0 ≤ θ) :
    transportWorst Ξ (WassersteinDRO.Duality.empiricalDistribution data) θ
        (truncated Z (extendFrom Ξ g)) =
      transportWorst Z (WassersteinDRO.Duality.empiricalDistribution data) θ
        (fun z => (extendFrom Ξ g z : EReal)) := by sorry

end BSSSampleRobust.Asymptotic
