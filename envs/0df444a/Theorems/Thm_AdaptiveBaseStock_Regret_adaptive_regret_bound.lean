-- Prove2me | Theorems.Thm_AdaptiveBaseStock_Regret_adaptive_regret_bound
-- name    : AdaptiveBaseStock.Regret.adaptive_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:17.431734+00:00
-- url     : https://prove2.me/theorems/6ed7e85d-34c3-490a-bb50-d70c896b4a02
-- title:
--   Theorem 10 (corrected) — explicit bound on the per-period regret Λ(L)/N(L) of Adaptive(α, β)
-- statement:
--   Consider the periodic-review lost-sales inventory system with lead time $\tau \ge 1$, holding cost $h > 0$, lost-sales penalty $b > 0$, and i.i.d. nonnegative continuous demand with $E[D] > 0$ and infinite support. Suppose Assumption 1 holds: $S^*$ minimizes the long-run average cost $C(I_\infty(\cdot))$ over $[0,\infty)$, $0 \le \underline M \le S^* \le \overline M$, and $\gamma(\underline M) = \mathcal P[D \le \underline M/(\tau+1)] > 0$. Run $\textsc{Adaptive}(\alpha,\beta)$ with $\alpha, \beta \in (0,1)$ from a level $S_1 \in [\underline M, \overline M]$ and an initial inventory vector $X_{(1,1)} \in \mathbb R^\tau_+$ with $X_{(1,1)}\cdot \mathbf 1^\tau \le \overline M$. Let
--   $$\nu = \max\{1 - \gamma(\underline M)^{2\tau}, F(\overline M), 1/e\}.$$
--   Then for every $L \ge 1$, writing $N = N(L)$,
--   $$\frac{\Lambda(L)}{N} \le (b+h)\Big[(\overline M - \underline M)\Big(\frac{C_1}{N^{\frac{1-\alpha}{1+\beta}}} + \frac{C_2}{N^{\frac{\alpha}{1+\beta}}} + \frac{C_3}{N^{\frac{1}{1+\beta}}}\Big) + \overline M\, \frac{C_4}{N^{\frac{\beta}{1+\beta}}}\Big],$$
--   with
--   $$C_1 = 4,\quad C_2 = \frac{4}{1-\alpha},\quad C_3 = \frac{12\,(4\tau)^{1/\beta}\,\Gamma(1/\beta)\,(1/\beta)}{(\ln(1/\nu))^{1/\beta}},\quad C_4 = \frac{24\tau}{\ln(1/\nu)} .$$
--
--   The algorithm observes only sales, never demand, and the bound compares its expected cost over $N(L)$ periods with $N(L)$ times the optimal long-run average base-stock cost. With $\alpha = \beta = 1/2$ every exponent equals $1/3$, so the per-period regret is $O(N(L)^{-1/3})$.
--
--   **Formalization Note** The paper prints the factor $(\overline M - \underline M)$ in front of all four terms. That bound is false: with $\underline M = \overline M = S^*$, $X_{(1,1)} = 0$ and $L = 1$ the right-hand side is $0$, while $\Lambda(1) = C(0) - C(I_\infty(S^*)) > 0$. The error is in Lemma 15, whose transient term scales with $\overline M$; the $C_4$ term therefore carries $\overline M$, and the $C_1$–$C_3$ terms keep $\overline M - \underline M$. Lean cycles are numbered from $1$, periods from $0$. The regret uses the long-run cost $C(I_\infty(S^*))$ of the model definition; integrability of every expectation follows from the boundedness of the inventory and is not assumed.
-- source:
--   Huh, Janakiraman, Muckstadt, Rusmevichientong, An Adaptive Algorithm for Finding the Optimal Base-Stock Policy in Lost Sales Inventory Systems with Censored Demand, working paper, February 8, 2007 (published version: Math. Oper. Res., 2009, DOI 10.1287/moor.1080.0367), Theorem 10, p. 24 (Assumption 1, p. 21; proof Sec. 5.3, pp. 25–29)

import Mathlib
import Definitions.Def_AdaptiveBaseStock_Regret_Algorithm

namespace AdaptiveBaseStock.Regret

open MeasureTheory ProbabilityTheory

/-- Theorem 10, p. 24, corrected on the `C₄` term: under Assumption 1, with continuous i.i.d.
demand of infinite support and `α, β ∈ (0, 1)`, the per-period regret of `Adaptive(α, β)` after
`L ≥ 1` cycles satisfies
`Λ(L)/N(L) ≤ (b + h) [(M̄ - M̲)(C₁/N^{(1-α)/(1+β)} + C₂/N^{α/(1+β)} + C₃/N^{1/(1+β)})
  + M̄ · C₄/N^{β/(1+β)}]`
with `C₁ = 4`, `C₂ = 4/(1-α)`, `C₃ = 12 (4τ)^{1/β} Γ(1/β)(1/β) / (ln(1/ν))^{1/β}`,
`C₄ = 24τ / ln(1/ν)` and `ν = max{1 - γ(M̲)^{2τ}, F(M̄), 1/e}`. The printed bound has the factor
`M̄ - M̲` on the `C₄` term as well, and is false. -/
theorem adaptive_regret_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (hD : IsDemandModel P D) (hinf : HasInfiniteSupport P (D 0))
    (τ : ℕ) (hτ : 1 ≤ τ) (p : AdaptiveParams τ) (hh : 0 < p.h) (hb : 0 < p.b)
    (hα0 : 0 < p.α) (hα1 : p.α < 1) (hβ0 : 0 < p.β) (hβ1 : p.β < 1)
    (Sstar : ℝ) (hMlo : 0 ≤ p.Mlo) (hlo : p.Mlo ≤ Sstar) (hhi : Sstar ≤ p.Mhi)
    (hγ : 0 < gammaLevel P (D 0) τ p.Mlo)
    (hopt : IsMinOn (baseStockCost P D τ p.h p.b) (Set.Ici 0) Sstar)
    (hS₁ : p.S₁ ∈ Set.Icc p.Mlo p.Mhi) (hx₁ : IsNonneg p.x₁) (hx₁M : position p.x₁ ≤ p.Mhi)
    (L : ℕ) (hL : 1 ≤ L) :
    regret P D p Sstar L / (periodsUpTo p.β L : ℝ)
      ≤ (p.b + p.h) *
          ((p.Mhi - p.Mlo) *
              (4 / (periodsUpTo p.β L : ℝ) ^ ((1 - p.α) / (1 + p.β))
                + 4 / (1 - p.α) / (periodsUpTo p.β L : ℝ) ^ (p.α / (1 + p.β))
                + 12 * (4 * (τ : ℝ)) ^ (1 / p.β) * Real.Gamma (1 / p.β) * (1 / p.β)
                    / (Real.log (1 / nu P (D 0) τ p.Mlo p.Mhi)) ^ (1 / p.β)
                    / (periodsUpTo p.β L : ℝ) ^ (1 / (1 + p.β)))
            + p.Mhi * (24 * (τ : ℝ) / Real.log (1 / nu P (D 0) τ p.Mlo p.Mhi))
                / (periodsUpTo p.β L : ℝ) ^ (p.β / (1 + p.β))) := by sorry

end AdaptiveBaseStock.Regret
