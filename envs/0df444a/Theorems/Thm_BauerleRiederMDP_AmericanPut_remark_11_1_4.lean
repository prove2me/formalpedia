-- Prove2me | Theorems.Thm_BauerleRiederMDP_AmericanPut_remark_11_1_4
-- name    : BauerleRiederMDP.AmericanPut.remark_11_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:21.707067+00:00
-- url     : https://prove2.me/theorems/04f861c0-72a2-4c7f-9222-1ccc0bb649e4
-- title:
--   Remark 11.1.4 — for $\beta<1$: $P=J_\infty=J=J_{f^*}$, $P$ is the unique bounded fixed point, $\tau^*$ is optimal but not always finite
-- statement:
--   In the setting of Theorem 11.1.3 (binomial market with $d<1+i<u$, strike $K>0$, $E=\mathbb R_+$), suppose the discount factor $\beta=(1+i)^{-1}$ is less than one, i.e. $i>0$. Then:
--
--   1. $P=J_\infty=J=J_{f^*}$ on $E$, where $J_\infty$ is the value of the positive stopping Markov Decision Model over Markov policies, $J=\lim_n J_n$, and $J_{f^*}=\lim_n\mathcal T^n_{f^*}0$ with $f^*=1_{E^*}$;
--   2. $P$ is the unique bounded solution of $P=\mathcal TP$ on $E$: $P$ is bounded and solves the equation, and every bounded $w$ with $w=\mathcal Tw$ on $E$ equals $P$ on $E$;
--   3. the exercise time $\tau^*:=\inf\{n\in\mathbb N_0\mid X_n\in E^*\}$ is optimal for every $x\in E$.
--
--   Moreover $\tau^*$ is not finite in general: there are a binomial market with $i>0$, a strike $K>0$ and an initial price $x\in E$ with $\mathbb Q_x(\tau^*=\infty)>0$.
--
--   In the discounted case the hypothesis of Theorem 11.1.3 d) is automatically satisfied, so the perpetual put always has the optimal exercise time $\tau^*$, although the optimal holder may never exercise.
--
--   **Formalization Note** $J_\infty$ is `markovValue`, $J_n$ the iterates of `putT`, $J_{f^*}$ is `exerciseValue` of $E^*$, and $\tau^*$ is `policyTime` of the stationary rule $E^*$. Boundedness means boundedness on $E$.
--
--   Differences from the source:
--   - reading: strike K (sign not stated) → hypothesis 0 < K; reason: a strike price is positive (as in Theorem 11.1.3)
--   - encoding: β = (1 + i)⁻¹ less than one → 0 < i; reason: equivalent for i ≥ 0
--   - encoding: J_∞, the value of the infinite-stage positive MDM → markovValue: supremum over Markov policies with measurable exercise sets of the expected discounted reward; reason: the value of the stopping MDM of §10.1 / §11.1 with reward earned once at the exercise time
--   - reading: 'τ* is not finite in general' → ∃ market with i > 0, K > 0, x ≥ 0 such that ℚ(τ* = ∞) > 0; reason: the remark asserts that finiteness can fail; an instance where it fails with positive probability is the content
--   - encoding: 𝔼^ℚ_x and sup_τ as real numbers, on the probability space of the market → lower Lebesgue integrals in ℝ≥0∞ on the coin space ℕ → Bool under the product law pathLaw; P is toReal of the ℝ≥0∞ supremum; reason: the integrand is nonnegative and bounded by K on E, so the supremum is finite and the values agree
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, Remark 11.1.4, p.338, PDF 346

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_putT
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_exerciseValue
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_exerciseRegion
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_markovValue

open MeasureTheory Filter Topology
open scoped ENNReal
open FinancialDerivatives.FD04 (putPayoff)

namespace BauerleRiederMDP.AmericanPut

/-- **Remark 11.1.4** (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.338,
PDF 346): if the discount factor `β = (1 + i)⁻¹` is less than one, then `P = J_∞ = J = J_{f*}`; in this case
`P(x)` is the unique bounded solution of `P = 𝒯P`; moreover the exercise time `τ*` is optimal, but `τ*` is not
finite in general.

**Formalization Note.** `β < 1` is `0 < i`. `J_∞` is `markovValue` (supremum over Markov exercise policies of
the positive stopping MDP), `J = lim J_n` is the limit of `(putT M K)^[n] (putPayoff K)`, `J_{f*}` is
`exerciseValue` of `E*`, all on `E = ℝ₊`; boundedness is boundedness on `E`. "Not finite in general" is the
last conjunct: some binomial market with `i > 0`, strike `K > 0` and initial price `x ∈ E` has
`ℚ(τ* = ∞) > 0`. -/
theorem remark_11_1_4 :
    (∀ (M : BinomialMarket) (K : ℝ), 0 < K → 0 < M.i →
      (∀ x : ℝ, 0 ≤ x → M.perpetualPut K x = M.markovValue K x) ∧
      (∀ x : ℝ, 0 ≤ x →
        Tendsto (fun n : ℕ => ((M.putT K)^[n] (putPayoff K)) x) atTop (𝓝 (M.perpetualPut K x))) ∧
      (∀ x : ℝ, 0 ≤ x → M.perpetualPut K x = M.exerciseValue K (M.exerciseRegion K) x) ∧
      ((∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → |M.perpetualPut K x| ≤ C) ∧
        (∀ x : ℝ, 0 ≤ x → M.perpetualPut K x = M.putT K (M.perpetualPut K) x) ∧
        ∀ w : ℝ → ℝ, (∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → |w x| ≤ C) →
          (∀ x : ℝ, 0 ≤ x → w x = M.putT K w x) → ∀ x : ℝ, 0 ≤ x → w x = M.perpetualPut K x) ∧
      (∀ x : ℝ, 0 ≤ x → IsStoppingTime (M.policyTime x (fun _ => M.exerciseRegion K)) ∧
        M.putReward K x (M.policyTime x (fun _ => M.exerciseRegion K)) =
          ⨆ τ : {τ : (ℕ → Bool) → ℕ∞ // IsStoppingTime τ}, M.putReward K x τ.1)) ∧
    (∃ (M : BinomialMarket) (K : ℝ), 0 < K ∧ 0 < M.i ∧ ∃ x : ℝ, 0 ≤ x ∧
      0 < M.pathLaw {ω | M.policyTime x (fun _ => M.exerciseRegion K) ω = ⊤}) := by sorry

end BauerleRiederMDP.AmericanPut
