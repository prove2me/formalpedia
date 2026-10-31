-- Prove2me | Theorems.Thm_CompetitionComplexity_proposition_1
-- name    : CompetitionComplexity.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:58.755+00:00
-- url     : https://prove2.me/theorems/e665ca07-b298-4b8a-80a8-a48e6477d740
-- title:
--   Proposition 1 — increment formulas for $A_n(F)$, $\lim_n A_n(F)=\omega_1(F)$, and strict increase when $\omega_0(F)<\omega_1(F)$
-- statement:
--   Let $F$ be a distribution on $[0,\infty)$ with finite mean, with distribution function $F(y)$, support endpoints $\omega_0(F)=\inf\{y:F(y)>0\}$ and $\omega_1(F)=\sup\{y:F(y)<1\}$, and let $A_n(F)$ be the optimal dynamic pricing value ($A_0=0$, $A_{n+1}=\mathbb E\max\{X,A_n\}$). Then:
--
--   1. for every $n\in\mathbb N$,
--   $$A_{n+1}(F)=A_n(F)+\int_{A_n(F)}^{\infty}\bigl(1-F(y)\bigr)\,dy;$$
--   2. for every $n\in\mathbb N$,
--   $$A_{n+2}(F)=A_{n+1}(F)+\int_{A_n(F)}^{A_{n+1}(F)}F(y)\,dy;$$
--   3. $\lim_{n\to\infty}A_n(F)=\omega_1(F)$ (possibly $+\infty$);
--   4. if $\omega_0(F)<\omega_1(F)$, then $A_n(F)<A_{n+1}(F)$ for every $n\in\mathbb N$.
--
--   Parts 1–2 express the increments of the dynamic program through the distribution function; they drive Lemmas 1–3.
--
--   Differences from the source:
--   - encoding: ω₁(F) ∈ ℝ ∪ {+∞} and lim Aₙ(F) = ω₁(F) → ω₁ valued in EReal; convergence of (Aₙ(F) : EReal) to ω₁(F) in EReal; reason: represents ω₁(F) = +∞; same instances
--   - encoding: ∫_{Aₙ(F)}^∞ (1 − F(y))dy → Lebesgue integral of 1 − F over (Aₙ(F), ∞); reason: the integrand is integrable there because F has finite mean; the endpoint is a null set
--   - encoding: (iv) "If ω0(F) < ω1(F) and F has finite expectation" → hypothesis ω₀ < ω₁ only; reason: finite expectation is part of the standing class of distributions, which every clause assumes
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, Proposition 1, p.8

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting
import Definitions.Def_CompetitionComplexity_Distribution

open MeasureTheory ProbabilityTheory Filter Topology
open CorreaThreshold.Adaptive (dpW)

namespace CompetitionComplexity

/-- **Proposition 1** (the optimal policy).
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), Proposition 1, p.8:
"For every distribution F the following holds:
(i) An+1(F) = An(F) + ∫_{An(F)}^∞ (1 − F(y))dy for every n ∈ N.
(ii) An+2(F) = An+1(F) + ∫_{An(F)}^{An+1(F)} F(y)dy for every n ∈ N.
(iii) limn→∞ An(F) = ω1(F).
(iv) If ω0(F) < ω1(F) and F has finite expectation, then An(F) < An+1(F) for every n ∈ N."

**Formalization Note.** `F(y)` is `cdf μ y`; `∫_a^∞` is the integral over `(a, ∞)`; `ω₁(F)` is
`EReal`-valued (`+∞` for unbounded support), so (iii) is convergence in `EReal`. Finite expectation is
part of the standing class `IsDist`, so (iv) carries only `ω₀ < ω₁`. -/
theorem proposition_1 (μ : Measure ℝ) (hμ : IsDist μ) :
    (∀ n : ℕ, dpW μ (n + 1) = dpW μ n + ∫ y in Set.Ioi (dpW μ n), (1 - cdf μ y)) ∧
    (∀ n : ℕ, dpW μ (n + 2) = dpW μ (n + 1) + ∫ y in (dpW μ n)..(dpW μ (n + 1)), cdf μ y) ∧
    Tendsto (fun n => (dpW μ n : EReal)) atTop (𝓝 (omega1 μ)) ∧
    (omega0 μ < omega1 μ → ∀ n : ℕ, dpW μ n < dpW μ (n + 1)) := by sorry

end CompetitionComplexity
