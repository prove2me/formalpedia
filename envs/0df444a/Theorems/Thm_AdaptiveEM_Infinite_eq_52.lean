-- Prove2me | Theorems.Thm_AdaptiveEM_Infinite_eq_52
-- name    : AdaptiveEM.Infinite.eq_52
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:59.132439+00:00
-- url     : https://prove2.me/theorems/f8ca647c-f08a-48ca-80cb-878ee5584762
-- title:
--   (52) — $\mathbb E[e^{\lambda pt/2}\|e_t\|^p]\le 2(8(p-2)/(p\lambda))^{p/2-1}\int_0^t\mathbb E[\widehat L^{p/2}\|\widehat X_s-\overline X_s\|^p]e^{\lambda ps/2}\mathrm ds$
-- statement:
--   Assume the hypotheses of Theorem 6: $W$ is a $d$-dimensional $(\mathcal F_t)$-Brownian motion on a probability space; $f,g$ satisfy Assumption 9 with constants $p^*,\lambda,\eta$ and (14) with $\gamma,\mu,q$; $\|g(x)\|^2\le\beta_g$ for all $x$; $h$ satisfies Assumption 8; for a fixed $T>0$ and every $\delta\in(0,1]$ the timestep $h^\delta$ is measurable and satisfies Assumption 3; and $X$ solves $\mathrm dX_t=f(X_t)\mathrm dt+g(X_t)\mathrm dW_t$, $X_0=x_0$, on $[0,\infty)$. Let $\widehat X$, $\overline X$ be the interpolants of the scheme run with $h^\delta$, $e_t=\widehat X_t-X_t$, and
--   $$L(x,y)=\gamma(\|x\|^q+\|y\|^q)+\mu,\qquad \widehat L(x,y)=\frac2\lambda L(x,y)^2+\frac{(p-1)\eta}2+\frac{\eta^2(p-1)^2}\lambda.$$
--   Then for every $p\in(2,p^*]$, every $\delta\in(0,1]$ and every $t\ge0$,
--   $$
--   \mathbb E\big[e^{\lambda pt/2}\|e_t\|^p\big]\le2\Big(\frac{8(p-2)}{p\lambda}\Big)^{p/2-1}\int_0^t\mathbb E\Big[\widehat L(\widehat X_s,\overline X_s)^{p/2}\|\widehat X_s-\overline X_s\|^p\Big]e^{\lambda ps/2}\,\mathrm ds.
--   $$
--
--   The inequality transfers the contractivity (20) to the error: the weight $e^{\lambda pt/2}$ on the left is paid for by the same weight inside the integral, so a time-uniform bound on $\mathbb E[\widehat L^{p}]$ and on $\mathbb E\|\widehat X_s-\overline X_s\|^{2p}$ of order $\delta^p$ yields an error of order $\delta^{p/2}$ uniformly in $t$.
--
--   **Formalization Note** Expectations and the time integral are lower Lebesgue integrals in $[0,\infty]$. The factor $p-2$ requires $p>2$, so the statement is for $p\in(2,p^*]$ (Assumption 9 has $p^*>2$). The constant $2(8(p-2)/(p\lambda))^{p/2-1}$ and $\widehat L$ are exactly the source's.
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 558, (52) (§6.4, proof of Theorem 6; e_t and L defined on p. 557, L̂ on p. 558)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Scheme
import Definitions.Def_AdaptiveEM_Infinite_Assumptions

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace AdaptiveEM.Infinite

open EthierKurtz SabanisEuler.Shared

/-- Fang–Giles (2020), p. 558, (52) (§6.4, proof of Theorem 6): under the hypotheses of
Theorem 6 (Assumption 9, `g` bounded (18), `h` with Assumption 8, `h^δ` with Assumption 3
for a fixed `T > 0`), for `p ∈ (2, p*]`, `δ ∈ (0, 1]` and `t ≥ 0`, with `e_t = X̂_t − X_t`,
`L(x, y) = γ(‖x‖^q + ‖y‖^q) + μ` and `L̂(x, y) = (2/λ)L(x, y)² + (p−1)η/2 + η²(p−1)²/λ`:
`E[e^{λpt/2}‖e_t‖^p] ≤ 2(8(p − 2)/(pλ))^{p/2−1} ∫_0^t E[L̂(X̂_s, X̄_s)^{p/2}‖X̂_s − X̄_s‖^p] e^{λps/2} ds`.
All expectations and the time integral are lower Lebesgue integrals in `[0, ∞]`. -/
theorem eq_52 {m d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → SDEState d) (hW : IsWienerMartingale P ℱ W)
    (f : SDEState m → SDEState m) (g : SDEState m → Diffusion m d) (x0 : SDEState m)
    (pstar lam η γ μ q : ℝ) (hA9 : Assumption9 f g pstar lam η γ μ q)
    (βg : ℝ) (h18 : ∀ x : SDEState m, ‖g x‖ ^ 2 ≤ βg)
    (h : SDEState m → ℝ) (hmax α β : ℝ) (hA8 : Assumption8 f h hmax α β)
    (T : ℝ) (hT : 0 < T) (hδ : ℝ → SDEState m → ℝ)
    (hA3 : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → Assumption3 h T δ (hδ δ) ∧ Measurable (hδ δ))
    (X : ℝ≥0 → Ω → SDEState m)
    (hX : ∀ T' : ℝ≥0, IsSolution P ℱ W T' (fun _ => x0) (fun z => f z.2) (fun z => g z.2) X) :
    ∀ p : ℝ, 2 < p → p ≤ pstar → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ t : ℝ≥0,
      let Lhat : SDEState m → SDEState m → ℝ := fun x y =>
        2 / lam * (γ * (‖x‖ ^ q + ‖y‖ ^ q) + μ) ^ 2 + (p - 1) * η / 2
          + η ^ 2 * (p - 1) ^ 2 / lam
      ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * p * (t : ℝ) / 2))
          * ‖AdaptiveEM.Finite.Xhat f g (hδ δ) x0 W t ω - X t ω‖ₑ ^ p ∂P
        ≤ ENNReal.ofReal (2 * (8 * (p - 2) / (p * lam)) ^ (p / 2 - 1))
          * ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
              (∫⁻ ω, ENNReal.ofReal
                  (Lhat (AdaptiveEM.Finite.Xhat f g (hδ δ) x0 W s.toNNReal ω) (AdaptiveEM.Finite.Xbar f g (hδ δ) x0 W s.toNNReal ω)
                    ^ (p / 2))
                * ‖AdaptiveEM.Finite.Xhat f g (hδ δ) x0 W s.toNNReal ω - AdaptiveEM.Finite.Xbar f g (hδ δ) x0 W s.toNNReal ω‖ₑ ^ p ∂P)
              * ENNReal.ofReal (Real.exp (lam * p * s / 2)) := by sorry

end AdaptiveEM.Infinite
