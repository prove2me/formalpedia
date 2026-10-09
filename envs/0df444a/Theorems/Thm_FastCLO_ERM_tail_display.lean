-- Prove2me | Theorems.Thm_FastCLO_ERM_tail_display
-- name    : FastCLO.ERM.tail_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:21:17.742265+00:00
-- url     : https://prove2.me/theorems/d164c3fa-b949-4e71-aeed-930ec630be69
-- title:
--   Proof of Theorem 6, p. 27 — tail bound P(d(π*, π̂^ERM) ≥ ktε_n²) ≤ exp(−t) for all t ≥ 1
-- statement:
--   Let $\alpha, \gamma \ge 0$. There are constants $K, c > 0$, depending only on $\alpha$ and $\gamma$, with the following property. Let $\mathcal Z$ be a polytope with norm bound $B$ and extreme points $\mathcal Z^\angle$, and fix an instance satisfying the noise condition (Assumption 2) with $\alpha, \gamma$ and $\mathbb P(|\mathcal Z^*(X)| > 1) = 0$. Let $\Pi \subseteq [\mathbb R^p \to \mathcal Z^\angle]$ have Natarajan dimension at most $\eta$, with $\eta \ge 1$, and contain a policy $\pi^*$ that is optimal for almost every $x$. Let $\hat\pi^{\mathrm{ERM}}_\Pi$ be an empirical risk minimizer over $\Pi$, measurable jointly in the data and the feature. Put $\bar V = 5\eta\log(|\mathcal Z^\angle|^2 + 1)$. If $n \ge 1$ and $n \ge c\,\bar V\log(n + 1)$, then for every $t \ge 1$,
--
--   $$\mathbb P_{\mathcal D}\left(d(\pi^*, \hat\pi^{\mathrm{ERM}}_\Pi) \ge K t\left(\frac{\bar V\log(n + 1)}{n}\right)^{\frac{1+\alpha}{2+\alpha}}\right) \le \exp(-t).$$
--
--   Integrating this tail bound over $t$ gives Theorem 6.
--
--   **Formalization Note** The paper writes the event as $d(\pi^*, \hat\pi) \ge k t \epsilon_n^2$ with $\epsilon_n = (c_2\sqrt{\bar V\log(n + 1)/n})^{(1+\alpha)/(2+\alpha)}$, valid when $n \ge c_2^{-\alpha}(4C_0^2/c_1)^{(2+\alpha)/2}\bar V\log(n + 1)$; the constants $k, c_2, c_1$ (depending on $\alpha, \gamma$) and the universal $C_0$ are packed into $K = k c_2^{(2+2\alpha)/(2+\alpha)}$ and $c = c_2^{-\alpha}(4C_0^2/c_1)^{(2+\alpha)/2}$. The hypothesis $\eta \ge 1$ is the paper's $\epsilon_n > 0$: at $\eta = 0$ the threshold is $0$ and the event is sure.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, proof of Theorem 6, A.4.3, p. 27, last display

import Mathlib
import Definitions.Def_FastCLO_ERM_ERM
import Definitions.Def_FastCLO_ERM_NatShatters
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace FastCLO.ERM

/-- **Tail bound for ERM** (Hu, Kallus, Mao, *Fast Rates for Contextual Linear Optimization*,
arXiv:2011.03030v3, proof of Theorem 6, A.4.3, p. 27, last display: "Combining with Eq. (19) we get
for all t ≥ 1, P(d(π*, π̂^ERM_Π) ≥ ktε_n²) ≤ exp(−t)"). Under the hypotheses of Theorem 6, with
`V̄ = 5η log(|Z∠|² + 1)` and `ε_n² = c₂^{(2+2α)/(2+α)} (V̄ log(n+1)/n)^{(1+α)/(2+α)}`, whenever
`n ≥ c₂^{−α}(4C₀²/c₁)^{(2+α)/2} V̄ log(n + 1)`, for all `t ≥ 1`
`P_D(d(π*, π̂^ERM) ≥ k t ε_n²) ≤ exp(−t)`.

Formalization Note: the page's constants `k`, `c₂` (depending only on `α, γ`) and the universal `C₀`
are packed into `K = k c₂^{(2+2α)/(2+α)}` and `c = c₂^{−α}(4C₀²/c₁)^{(2+α)/2}`, both chosen before
the instance. `1 ≤ η` is the page's `ε_n > 0` (at `η = 0`, `ε_n = 0` and the event `d ≥ 0` is
sure). `π* ∈ Π` is read as: some member of `Π` is optimal at almost every `x`. The ERM algorithm is
any selection from the empirical argmin over the whole class, jointly measurable in the data and
the feature; `1 ≤ n` because the page divides by `n`. -/
theorem tail_display (α γ : ℝ) (hα : 0 ≤ α) (hγ : 0 ≤ γ) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ (p d : ℕ) (P : Polytope d) (I : Instance p d)
      (PC : Set (Vec p → Vec d)) (η n : ℕ) (alg : (Fin n → Vec p × Vec d) → Vec p → Vec d)
      (πs : Vec p → Vec d),
      1 ≤ n → 1 ≤ η →
      NoiseCond P I α γ →
      (∀ᵐ x ∂I.μ, (Zstar P I x).Subsingleton) →
      (∀ π ∈ PC, IsPolicy P π) →
      ¬ NatShatters PC (η + 1) →
      πs ∈ PC → (∀ᵐ x ∂I.μ, πs x ∈ Zstar P I x) →
      (∀ D, IsERM PC D (alg D)) →
      Measurable (Function.uncurry alg) →
      c * (5 * (η : ℝ) * Real.log ((P.ext.ncard : ℝ) ^ 2 + 1)) * Real.log ((n : ℝ) + 1)
          ≤ (n : ℝ) →
      ∀ t : ℝ, 1 ≤ t →
        I.sample n {D | K * t * (5 * (η : ℝ) * Real.log ((P.ext.ncard : ℝ) ^ 2 + 1)
              * Real.log ((n : ℝ) + 1) / n) ^ ((1 + α) / (2 + α)) ≤ dExcess P I πs (alg D)}
          ≤ ENNReal.ofReal (Real.exp (-t)) := by sorry

end FastCLO.ERM
