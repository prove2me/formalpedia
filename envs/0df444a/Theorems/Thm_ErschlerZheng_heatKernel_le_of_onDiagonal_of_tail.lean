-- Prove2me | Theorems.Thm_ErschlerZheng_heatKernel_le_of_onDiagonal_of_tail
-- name    : ErschlerZheng.heatKernel_le_of_onDiagonal_of_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-04T11:32:05.30498+00:00
-- url     : https://prove2.me/theorems/00d6bc4e-5997-442c-b75d-0267566ecf0b
-- title:
--   Erschler–Zheng, Proposition 7.20 (as proved, p. 52) — an on-diagonal bound and tail bounds on J give an off-diagonal heat kernel bound
-- statement:
--   For real numbers $C_0 > 0$, $c_\phi$ and $\beta > 0$ there is a constant $C > 0$, chosen before everything else and so depending only on $C_0$, $c_\phi$ and $\beta$, with the following property. Let $X$ be a countable set, $J$ a symmetric transition kernel on $X$ (`IsTransition J`, `IsSymmetric J`), $\rho$ a metric on $X$ (`IsMetric ρ`) and $\phi : \mathbb R \to \mathbb R$ a function, and suppose:
--
--   - (i) $p(t,x,x) \le C_0/t^{1/\beta}$ for every real $t > 0$ and every $x \in X$, where $p(t,x,y) = \sum_{n\ge0}e^{-t}\frac{t^n}{n!}J^n(x,y)$ (`heatKernel J t x y`) is the heat kernel of $J$, the transition function of the continuous-time walk with jump kernel $J$;
--   - (ii) $\phi(r) > 0$ for every $r > 0$; $\phi$ is non-decreasing on $(0,\infty)$ (`MonotoneOn φ (Set.Ioi 0)`); $\phi(2r) \le c_\phi\,\phi(r)$ for every $r > 0$; and for every $x \in X$ and every $r > 0$,
--   $$\sum_{y:\ \rho(x,y) > r}J(x,y) \le \frac{1}{\phi(r)},$$
--   $$\sum_{y:\ \rho(x,y) \le r}\rho(x,y)^2J(x,y) \le \frac{r^2}{\phi(r)}.$$
--
--   Then for all $x \ne y$ in $X$ and every real $t$ with $0 < t \le \phi(\rho(x,y))$,
--   $$p(t,x,y) \le \frac{C\,t}{\phi(\rho(x,y))^{1+1/\beta}} + t\,\sup\{J(u,v) : \rho(u,v) > R\},$$
--   where $R = \beta\rho(x,y)/(3(1+\beta))$. The supremum (`supNorm (farPart J ρ R)`) runs over all pairs $(u,v)$ of $X$, not only those involving $x$ or $y$, and is $0$ if there are none. The inequality is stated in $[0,\infty]$; all its terms are finite and non-negative, so it is the real inequality displayed. The values of $\phi$ at $r \le 0$ play no role.
--
--   A. Erschler and T. Zheng, *Growth of periodic Grigorchuk groups*, Invent. Math. 219 (2020) 1069–1155, [doi:10.1007/s00222-019-00922-0](https://doi.org/10.1007/s00222-019-00922-0), with the page numbers of [arXiv:1802.09077v2](https://arxiv.org/abs/1802.09077v2), state on p. 49: “**Proposition 7.20** ([4]). Let $J(x,y)$ be a symmetric transition kernel on a countable set $X$ and let $\rho$ be a metric on $X$. Suppose (i): There exists $0 < C_0 < \infty$ and $\beta > 0$ such that for all $t > 0$, we have $\sup_{x\in X}p(t,x,x) \leqslant \frac{C_0}{t^{1/\beta}}$. (ii): There exists an increasing function $\phi : (0,\infty) \to (0,\infty)$ such that $\phi(2r) \leqslant c_\phi\phi(r)$ for all $r > 0$ and for all $x \in X$, $r > 0$, $\sum_{y\in X}J(x,y)\mathbf 1_{\{\rho(x,y)>r\}} \leqslant \frac{1}{\phi(r)}$, $\sum_{y\in X}\rho^2(x,y)J(x,y)\mathbf 1_{\{\rho(x,y)\leqslant r\}} \leqslant \frac{r^2}{\phi(r)}$. Then there exists a constant $C = C(C_0, c_\phi, \beta) > 0$ such that for any $x, y \in X$ and $t \leqslant \phi(\rho(x,y))$, $p(t,x,y) \leqslant \frac{Ct}{\phi(\rho(x,y))^{1+\frac1\beta}} + t\sup_{\rho(u,v)\geqslant\rho(x,y)}J(u,v)$.” Before the statement they define $p$: “Let $P_t$ be the associated heat semigroup and $p(t,x,y)$ its transition density.” The proof (pp. 51–52) ends: “Choose $\lambda$ and $R$ to be $R = \frac{\beta}{3(1+\beta)}\rho(x_0,y_0)$, $\lambda = \frac{1}{3R}\log\left(\frac{\phi(R)}{t}\right)$. We conclude that for $t \leqslant \phi(\rho(x,y))$, $p_R(t,x,y) \leqslant \frac{Ct}{\phi(\rho(x,y))^{1+1/\beta}}$. The statement is obtained by combining this bound with (7.14).”
--
--   The supremum here is the one the proof gives. The bound (7.14), $p(t,x,y) \leqslant p_R(t,x,y) + t\|J_2^R\|_\infty$ (`BarlowGrigoryanKumagai.heatKernel_le_heatKernel_nearPart_add`), contributes the supremum of $J(u,v)$ over $\rho(u,v) > R$, with $R = \beta\rho(x,y)/(3(1+\beta)) < \rho(x,y)$. That set of pairs contains the printed one, $\rho(u,v) \geqslant \rho(x,y)$, so this statement is weaker than the printed proposition: its threshold is the fixed fraction $\beta/(3(1+\beta))$ of $\rho(x,y)$. The other readings of the printed statement:
--
--   - “Increasing” is read as non-decreasing, with $\phi$ positive on $(0,\infty)$.
--   - Points $x = y$ are excluded: there $\phi(\rho(x,y)) = \phi(0)$, outside the domain $(0,\infty)$ of the printed $\phi$.
--   - Times $t \le 0$ are excluded, as in (i).
--   - The transition density is taken with respect to the counting measure, so it is the transition probability `heatKernel J t x y`.
--
--   The proof on pp. 51–52 combines (7.14), the Nash inequality for $J^R_1$ (`Coulhon.nash_of_heatKernel_le`) and the bound (7.15) (`CarlenKusuokaStroock.heatKernel_le_exp_davies`) with $\psi(x) = \lambda(\rho(x,x_0) - \rho(x,y_0))_+$ for a parameter $\lambda > 0$ (p. 52). The printed choice $\lambda = \frac{1}{3R}\log(\phi(R)/t)$ is positive only when $t < \phi(R)$.
--
--   The formal proof imports those three theorems and follows this route, in the following form.
--
--   - The hypothesis of `Coulhon.nash_of_heatKernel_le` comes from two facts. The tail bound at $r = R$ gives $U \le J + \phi(R)^{-1}I$ entrywise, for $U$ = `uniformize (nearPart J ρ R)`, so $p_R(s,u,v) \le e^{s/\phi(R)}p(s,u,v)$. And (i) bounds $p(s,u,v) \le \frac12\bigl(p(s,u,u) + p(s,v,v)\bigr)$ by $C_0s^{-1/\beta}$.
--   - The weight is $\psi(z) = \lambda(\rho(x,y) - \rho(z,y))_+$. It has the same values at $x$ and $y$ as the printed one with $x_0 = x$, $y_0 = y$, and it is $\lambda$-Lipschitz. With the second-moment bound at $r = R$, this gives $\Lambda_R(\psi)^2 \le \lambda^2e^{2\lambda R}R^2/\phi(R)$.
--   - $\lambda$ is the printed choice when $t < \phi(R)$, and $\lambda = 0$ when $t \ge \phi(R)$.
--   - With $k = \lceil 3(1+\beta)/\beta\rceil$ and $Q = \max(1, c_\phi)^k$, doubling and monotonicity give $\phi(\rho(x,y)) \le Q\,\phi(R)$.
--
--   The constant is $C = C_2\,e^{4Q+144}\,Q^{1+1/\beta}$. Here $C_2$ is the constant of `CarlenKusuokaStroock.heatKernel_le_exp_davies` for the constant $C'$ that `Coulhon.nash_of_heatKernel_le` gives at $(C_0, \beta)$.
-- source:
--   A. Erschler and T. Zheng, Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 49, Proposition 7.20, with the range of the supremum given by its proof, p. 52

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels

universe u

open DurrettProbability MarkovChain

namespace ErschlerZheng

theorem heatKernel_le_of_onDiagonal_of_tail (C₀ cφ β : ℝ) (hC₀ : 0 < C₀) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type u) [Countable X] [DecidableEq X] (J ρ : X → X → ℝ)
      (φ : ℝ → ℝ),
      IsTransition J → IsSymmetric J → IsMetric ρ →
      (∀ t : ℝ, 0 < t → ∀ x, heatKernel J t x x ≤ C₀ / t ^ (1 / β)) →
      (∀ r : ℝ, 0 < r → 0 < φ r) → MonotoneOn φ (Set.Ioi 0) →
      (∀ r : ℝ, 0 < r → φ (2 * r) ≤ cφ * φ r) →
      (∀ x, ∀ r : ℝ, 0 < r → ∑' y, (if r < ρ x y then J x y else 0) ≤ 1 / φ r) →
      (∀ x, ∀ r : ℝ, 0 < r → ∑' y, (if ρ x y ≤ r then ρ x y ^ 2 * J x y else 0) ≤ r ^ 2 / φ r) →
      ∀ x y, x ≠ y → ∀ t : ℝ, 0 < t → t ≤ φ (ρ x y) →
        ENNReal.ofReal (heatKernel J t x y) ≤
          ENNReal.ofReal (C * t / φ (ρ x y) ^ (1 + 1 / β)) +
            ENNReal.ofReal t * supNorm (farPart J ρ (β * ρ x y / (3 * (1 + β)))) := by
  sorry

end ErschlerZheng
