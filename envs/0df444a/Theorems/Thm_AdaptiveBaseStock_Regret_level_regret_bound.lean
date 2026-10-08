-- Prove2me | Theorems.Thm_AdaptiveBaseStock_Regret_level_regret_bound
-- name    : AdaptiveBaseStock.Regret.level_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:11.85661+00:00
-- url     : https://prove2.me/theorems/2c8ba027-5434-4cdd-82a1-366e17e3e1c6
-- title:
--   Lemma 14 — bound on Λ₁(L), the regret from S_k ≠ S*
-- statement:
--   Consider $\textsc{Adaptive}(\alpha,\beta)$ with $\alpha, \beta \in (0,1)$ on the lost-sales system with lead time $\tau \ge 1$, costs $h, b > 0$, and i.i.d. nonnegative continuous demand with $E[D] > 0$ and infinite support. Suppose Assumption 1 holds: $S^*$ minimizes $C(I_\infty(\cdot))$ over $[0,\infty)$, $0 \le \underline M \le S^* \le \overline M$, and $\gamma(\underline M) > 0$; and the algorithm starts from $S_1 \in [\underline M, \overline M]$ and $X_{(1,1)} \in \mathbb R^\tau_+$ with $X_{(1,1)}\cdot\mathbf 1^\tau \le \overline M$. Let $\nu = \max\{1 - \gamma(\underline M)^{2\tau}, F(\overline M), 1/e\}$. Then for every $L \ge 1$,
--   $$\Lambda_1(L) \le (\overline M - \underline M)(b+h)\, T_L \Big\{\frac{L^\alpha}{2} + \frac{L^{1-\alpha}}{2(1-\alpha)} + 3\,\frac{(4\tau)^{1/\beta}\,\Gamma(1/\beta)\,(1/\beta)}{(\ln(1/\nu))^{1/\beta}}\Big\}.$$
--
--   This is the part of the regret due to the levels $S_k$ differing from $S^*$; it comes from the projected gradient bound of Theorem 11 together with the bias bounds of Theorems 3 and 8.
--
--   **Formalization Note** This keeps the lemma's printed constant. Its proof applies Theorem 3 to $\delta_{T_k}$ with exponent $\lceil k^\beta\rceil$, while Theorem 3 bounds $\delta_{t+1}$ with exponent $t$; that proof step needs repair, but the printed statement has not been disproved.
-- source:
--   Huh, Janakiraman, Muckstadt, Rusmevichientong, An Adaptive Algorithm for Finding the Optimal Base-Stock Policy in Lost Sales Inventory Systems with Censored Demand, working paper, February 8, 2007 (published version: Math. Oper. Res., 2009, DOI 10.1287/moor.1080.0367), Lemma 14, p. 26 (proof pp. 26–27)

import Mathlib
import Definitions.Def_AdaptiveBaseStock_Regret_Algorithm

namespace AdaptiveBaseStock.Regret

open MeasureTheory ProbabilityTheory

/-- Lemma 14, p. 26: under Assumption 1, with infinite support and `α, β ∈ (0, 1)`,
`Λ₁(L) ≤ (M̄ - M̲)(b + h) T_L {L^α/2 + L^{1-α}/(2(1-α))
  + 3 (4τ)^{1/β} Γ(1/β)(1/β) / (ln(1/ν))^{1/β}}`.
The paper's proof appears to have an indexing gap in its use of Theorem 3; this statement
retains the bound actually asserted by Lemma 14. -/
theorem level_regret_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (hD : IsDemandModel P D) (hinf : HasInfiniteSupport P (D 0))
    (τ : ℕ) (hτ : 1 ≤ τ) (p : AdaptiveParams τ) (hh : 0 < p.h) (hb : 0 < p.b)
    (hα0 : 0 < p.α) (hα1 : p.α < 1) (hβ0 : 0 < p.β) (hβ1 : p.β < 1)
    (Sstar : ℝ) (hMlo : 0 ≤ p.Mlo) (hlo : p.Mlo ≤ Sstar) (hhi : Sstar ≤ p.Mhi)
    (hγ : 0 < gammaLevel P (D 0) τ p.Mlo)
    (hopt : IsMinOn (baseStockCost P D τ p.h p.b) (Set.Ici 0) Sstar)
    (hS₁ : p.S₁ ∈ Set.Icc p.Mlo p.Mhi) (hx₁ : IsNonneg p.x₁) (hx₁M : position p.x₁ ≤ p.Mhi)
    (L : ℕ) (hL : 1 ≤ L) :
    regretLevel P D p Sstar L
      ≤ (p.Mhi - p.Mlo) * (p.b + p.h) * (cycleLen p.β L : ℝ) *
          ((L : ℝ) ^ p.α / 2 + (L : ℝ) ^ (1 - p.α) / (2 * (1 - p.α))
            + 3 * (4 * (τ : ℝ)) ^ (1 / p.β)
                * Real.Gamma (1 / p.β) * (1 / p.β)
                / (Real.log (1 / nu P (D 0) τ p.Mlo p.Mhi)) ^ (1 / p.β)) := by sorry

end AdaptiveBaseStock.Regret
