-- Prove2me | Theorems.Thm_EDPMBandit_theorem_4
-- name    : EDPMBandit.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:17.105782+00:00
-- url     : https://prove2.me/theorems/ab3155f6-ea9f-4a06-b39a-3dc466501eed
-- title:
--   Theorem 4 — U-UCB regret $O(\log T/T)$ for stable, smooth EDPMs with a linear gap
-- statement:
--   Fix $K$, parameters $\upsilon,b,q,\beta,\eta$, an exploration parameter $\gamma>2$, an arm $i^*$, and values $D$, $\rho$ and $\Delta_1,\dots,\Delta_K$. There is a horizon $T_1$, depending only on these problem parameters, with the following property.
--
--   Let $U$ be an EDPM that is stable with parameters $(\upsilon,b,q)$, smooth with $M_0=\infty$ and parameter $\beta$, and has a linear gap with parameter $\eta$; assume $\Delta_i>0$ for $i\ne i^*$, the standing measurability assumption, and that the diameter, the maximum gap ratio and the gaps of the instance are $D$, $\rho$ and $\Delta_i$. Put $L=b(1+D^{q-1})$. Then for every run of U-UCB, every admissible policy $\pi'$ and every $T\ge T_1$,
--
--   $$
--   \mathbb E\big[U(\hat F^{\pi'}_T)\big]-\mathbb E\big[U(\hat F^{U\text{-}UCB}_T)\big]\le\frac{L\rho}T\sum_{i\ne i^*}\Big(\frac{\gamma\Delta_i\log T}{\varphi(\Delta_i/2)}+\frac{\gamma+6}{\gamma-2}\Delta_i\Big)+\frac{12\beta K^2\log KT}{\upsilon T}.
--   $$
--
--   Taking $\pi'$ to be the finite-horizon oracle $\pi^*(T)$ of (7), the left-hand side is the regret $R_{U\text{-}UCB}(T)$ of (8): U-UCB has regret $O(\log T/T)$ for every stable, smooth objective with a linear gap.
--
--   **Formalization Note** Arms are `Fin K`; the reward stack $X$ is indexed from $0$ (the paper's $X_{i,k+1}$ is `X i k`); distribution functions are functions $\mathbb R\to\mathbb R$ in a submodule $L$ of $\mathbb R^{\mathbb R}$ with a seminorm $\|\cdot\|$; probabilities are values of the measure $P$ in $[0,\infty]$ and expectations are Bochner integrals; $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: distribution functions on the extended real line, in a seminormed space L containing all distributions → functions ℝ → ℝ; L any submodule of ℝ → ℝ containing every indicator 𝕀_{[a,∞)} and every distribution function, with a seminorm on L; reason: the values at ±∞ are 0 and 1 for every distribution; indicators are distribution functions of point masses, so the same spaces are allowed
--   - encoding: arms {1,…,K}, rewards X_{i,t} (t ≥ 1), admissible policies (1)–(3) with π_t H_{t−1}-measurable, natural log → arms Fin K, rewards X i k with zero-based sample index, policies as jointly measurable decision rules of V and the observed history; Real.log; reason: a choice is H_{t−1}-measurable iff it is a measurable function of (V, history) (Doob–Dynkin); same policy class
--   - generalization: R_{U−UCB}(T) = E[U(F̂^{π*(T)}_T) − U(F̂^{U−UCB}_T)] with π*(T) ∈ argmax_Π E U(F̂^π_T) (7)–(8) → E[U(F̂^{π'}_T)] − E[U(F̂^{U−UCB}_T)] for every admissible π'; reason: the oracle need not exist; where it does, π' = π*(T) gives the printed statement, and the proof never uses the optimality of π*(T)
--   - reading: for all T ≥ T₁, which is polynomial in problem parameters → ∃ T₁ : ℕ before the instance, depending only on K, υ, b, q, β, η, γ, i*, D, ρ, Δ; uniform over instances, U-UCB runs and comparators; reason: the explicit condition (29) contains log T on both sides and is not sufficient as printed, so "polynomial" has no literal content; this is the strongest form the clause has
--   - reading: Theorem 4 does not repeat the hypotheses of Theorem 2 → γ > 2 and Δ_i > 0 for i ≠ i*; reason: the printed bound is that of Theorem 2, whose hypotheses these are; ρ is undefined without Δ_i > 0
--   - reading: U-UCB (15): π_t ∈ argmax of the index for t ≥ K+1, each arm sampled once for t ≤ K, no tie-breaking rule → IsUUCBRun: an admissible policy with τ_i(K) = 1 for all i and the argmax property at every round t ≥ K+1 and every outcome; reason: U-UCB must be an admissible (non-anticipating) policy for the analysis; every non-anticipating tie-breaking and initial order is allowed
--   - reading: standing assumption (p.5): the expectations exist and are finite → MeasurableAlongEmp: x ↦ U(G + c·F̂_t(x)) and x ↦ ‖G + c·F̂_t(x)‖ are Borel measurable for all t, G, c; reason: makes every expectation the paper writes the integral of a measurable function; finiteness follows from stability
-- source:
--   Cassel–Mannor–Zeevi, A General Framework for Bandit Problems Beyond Cumulative Objectives, arXiv:1806.01380v3, p.10, Theorem 4 (proof p.28)

import Mathlib
import Definitions.Def_EDPMBandit_Model
import Definitions.Def_EDPMBandit_Conditions
import Definitions.Def_EDPMBandit_UUCB

open MeasureTheory ProbabilityTheory

namespace EDPMBandit

universe u v

/-- Theorem 4 (U − UCB regret), Cassel–Mannor–Zeevi, arXiv:1806.01380v3, p.10: "Suppose an EDPM,
U, is stable, smooth with M₀ = ∞, and has a linear gap. Letting L = b(1 + D^{q−1}), the regret of
running U − UCB is bounded as
R_{U−UCB}(T) ≤ (Lρ/T) ∑_{i≠i*} (γΔ_i log T/φ(Δ_i/2) + ((γ + 6)/(γ − 2)) Δ_i) + 12βK² log KT/(υT),
for all T ≥ T₁, which is polynomial in problem parameters."

**Formalization Note.**
* The regret (8) is centred at an oracle `π*(T) ∈ argmax_{π∈Π} E U(F̂^π_T)` (7); here the bound is
  stated against **every** admissible policy `π'` (where the oracle exists, `π' = π*(T)` is the
  printed statement).
* "for all T ≥ T₁, which is polynomial in problem parameters": there is `T₁` depending only on
  the problem parameters (`K`, `υ, b, q`, `β`, `η`, `γ`, the optimal arm `i*`, and the values
  `D`, `ρ`, `Δ_i`, which are fixed before `T₁` and pinned by hypotheses), uniform over all
  instances with these parameters, all U-UCB runs and all comparators.
* `γ > 2` and `Δ_i > 0` for `i ≠ i*` are the hypotheses of Theorem 2, whose bound is printed.
* Stability, smoothness (`M₀ = ∞`) and linear gap with fixed parameters; the standing
  measurability assumption of p.5 (`MeasurableAlongEmp`). `log KT = log (K·T)`, natural log. -/
theorem theorem_4 (K : ℕ) (υ b q β η γ : ℝ) (hγ : 2 < γ) (istar : Fin K) (D ρ : ℝ)
    (Δ : Fin K → ℝ) :
    ∃ T₁ : ℕ, ∀ (Ω : Type u) [MeasurableSpace Ω] (𝒱 : Type v) [MeasurableSpace 𝒱]
      (M : BanditModel K Ω 𝒱) (S : DistSpace) (N : Seminorm ℝ S.L) (U : S.L → ℝ),
      IsStable S N U M υ b q → IsSmoothInf S N U M β → HasLinearGap S N U M istar η →
      (∀ i, i ≠ istar → 0 < gap S U M istar i) → MeasurableAlongEmp S N U →
      diam S N M = D → gapRatio S N U M istar = ρ → (∀ i, gap S U M istar i = Δ i) →
      ∀ π : Policy K 𝒱, IsUUCBRun S U M υ b q γ π → ∀ π' : Policy K 𝒱, ∀ T : ℕ, T₁ ≤ T →
        (∫ ω, U (empPolicy S M π' T ω) ∂M.P) - (∫ ω, U (empPolicy S M π T ω) ∂M.P) ≤
          lipConst b q D * ρ / T *
              ∑ i ∈ Finset.univ.filter (· ≠ istar),
                (γ * Δ i * Real.log T / phi υ b q (Δ i / 2) + (γ + 6) / (γ - 2) * Δ i) +
            12 * β * (K : ℝ) ^ 2 * Real.log ((K : ℝ) * T) / (υ * T) := by sorry

end EDPMBandit
