-- Prove2me | Theorems.Thm_AdaptiveBaseStock_Regret_transient_regret_bound
-- name    : AdaptiveBaseStock.Regret.transient_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:21.566507+00:00
-- url     : https://prove2.me/theorems/c2403f6b-2426-4271-b701-430f24234c79
-- title:
--   Lemma 15 (corrected) — Λ₂(L) ≤ (b + h)·M̄·L·(12τ + 1)/ln(1/ν)
-- statement:
--   Under the hypotheses of Lemma 14 (Assumption 1, infinite support, $\alpha,\beta \in (0,1)$, and the algorithm's initialization), for every $L \ge 1$,
--   $$\Lambda_2(L) \le (b+h)\, \overline M\, L\, \frac{12\tau + 1}{\ln(1/\nu)}, \qquad \nu = \max\{1 - \gamma(\underline M)^{2\tau}, F(\overline M), 1/e\}.$$
--
--   $\Lambda_2$ measures how far the on-hand inventory inside each cycle is from the steady state of that cycle's level; the bound says each cycle contributes at most a constant, whatever its length.
--
--   **Formalization Note** The paper prints $\Lambda_2(L) \le (b+h)(\overline M - \underline M)\, L \cdot 12\tau/\ln(1/\nu)$, which is false: with $\underline M = \overline M = S^*$, $X_{(1,1)} = 0$ and $L = 1$ the right-hand side is $0$, while $\Lambda_2(1) = C(0) - C(I_\infty(S^*)) > 0$. The proof's bound $(\overline M - \underline M)\max\{b,h\}$ on $|E[C(I_{(k,j)})] - E[C(I_\infty(S_k))]|$ must be $\overline M \max\{b,h\}$, because on-hand stock ranges over $[0, \overline M]$; likewise Theorem 8 contributes $\max\{S_k, X_{(k,1)}\cdot\mathbf 1^\tau\} \le \overline M$. The constant $12\tau$ becomes $12\tau + 1$ because the paper applies Theorem 3 one period early: periods $j \le 4\tau + 1$ are bounded by Lipschitz continuity, the rest by Theorems 3 and 8.
-- source:
--   Huh, Janakiraman, Muckstadt, Rusmevichientong, An Adaptive Algorithm for Finding the Optimal Base-Stock Policy in Lost Sales Inventory Systems with Censored Demand, working paper, February 8, 2007 (published version: Math. Oper. Res., 2009, DOI 10.1287/moor.1080.0367), Lemma 15, p. 27 (proof pp. 27–28)

import Mathlib
import Definitions.Def_AdaptiveBaseStock_Regret_Algorithm

namespace AdaptiveBaseStock.Regret

open MeasureTheory ProbabilityTheory

/-- Lemma 15, p. 27, corrected: under Assumption 1, with infinite support and `α, β ∈ (0, 1)`,
`Λ₂(L) ≤ (b + h) · M̄ · L · (12τ + 1) / ln(1/ν)`. The printed bound
`(b + h)(M̄ - M̲) L · 12τ / ln(1/ν)` is false (it fails for `M̲ = M̄ = S*`, `X_(1,1) = 0`, `L = 1`). -/
theorem transient_regret_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (hD : IsDemandModel P D) (hinf : HasInfiniteSupport P (D 0))
    (τ : ℕ) (hτ : 1 ≤ τ) (p : AdaptiveParams τ) (hh : 0 < p.h) (hb : 0 < p.b)
    (hα0 : 0 < p.α) (hα1 : p.α < 1) (hβ0 : 0 < p.β) (hβ1 : p.β < 1)
    (Sstar : ℝ) (hMlo : 0 ≤ p.Mlo) (hlo : p.Mlo ≤ Sstar) (hhi : Sstar ≤ p.Mhi)
    (hγ : 0 < gammaLevel P (D 0) τ p.Mlo)
    (hopt : IsMinOn (baseStockCost P D τ p.h p.b) (Set.Ici 0) Sstar)
    (hS₁ : p.S₁ ∈ Set.Icc p.Mlo p.Mhi) (hx₁ : IsNonneg p.x₁) (hx₁M : position p.x₁ ≤ p.Mhi)
    (L : ℕ) (hL : 1 ≤ L) :
    regretTransient P D p L
      ≤ (p.b + p.h) * p.Mhi * (L : ℝ) * (12 * (τ : ℝ) + 1)
          / Real.log (1 / nu P (D 0) τ p.Mlo p.Mhi) := by sorry

end AdaptiveBaseStock.Regret
