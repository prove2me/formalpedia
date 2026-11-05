-- Prove2me | Theorems.Thm_BauerleRiederMDP_AmericanPut_theorem_11_1_3
-- name    : BauerleRiederMDP.AmericanPut.theorem_11_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:28.640102+00:00
-- url     : https://prove2.me/theorems/75c950b5-ab06-44ea-9ad5-ad8435d6476f
-- title:
--   Theorem 11.1.3 — the perpetual American put: value iteration, smallest superharmonic majorant, exercise below a threshold (corrected: e) needs $d<1$)
-- statement:
--   Consider the binomial market with interest rate $i\ge0$ and factors $0<d<1+i<u$, risk-neutral up probability $q=(1+i-d)/(u-d)$ and discount factor $\beta=(1+i)^{-1}\in(0,1]$. Let $K>0$ be the strike and
--   $$P(x):=\sup_{\tau\le\infty}\mathbb E^{\mathbb Q}_x\big[\beta^\tau(K-S_\tau)^+\big]$$
--   the price of the perpetual American put (reward $0$ on $\{\tau=\infty\}$), $E=\mathbb R_+$, and
--   $$\mathcal T v(x)=\max\Big\{(K-x)^+,\ \beta\big(q\,v(xu)+(1-q)\,v(xd)\big)\Big\},\qquad J_0=(K-x)^+,\quad J_n=\mathcal TJ_{n-1}.$$
--   Then:
--
--   1. **(a)** For every initial price $x>0$, $P(x)=J(x):=\lim_{n\to\infty}J_n(x)$.
--   2. **(b)** $P=\mathcal TP$ on $E$, and $0\le P(x)\le K$ for $x\in E$.
--   3. **(c)** $P$ is the smallest superharmonic function majorizing $(K-x)^+$: $P$ satisfies
--   $$P(x)\ge(K-x)^+,\qquad P(x)\ge\beta\big(qP(xu)+(1-q)P(xd)\big),\qquad x\in E,$$
--   and every function $v$ satisfying these two inequalities on $E$ has $P\le v$ on $E$.
--   4. **(d)** Let $E^*:=\{x\in E\mid P(x)=(K-x)^+\}$, $f^*=1_{E^*}$, and $J_{f^*}:=\lim_{n\to\infty}\mathcal T_{f^*}^n0$. If $J_{f^*}\ge\mathcal TJ_{f^*}$ on $E$, then $P=J_{f^*}$ on $E$ and
--   $$\tau^*:=\inf\{n\in\mathbb N_0\mid X_n\in E^*\}$$
--   is an optimal exercise time: it is a stopping time and its expected discounted payoff equals $P(x)$ for every $x\in E$.
--   5. **(e)** If moreover $d<1$, there is a constant $x^*\in[0,K]$ with
--   $$E^*=\{x\in E\mid x\le x^*\}.$$
--
--   The theorem identifies the perpetual put with the limit of the finite-horizon puts and with the least excessive majorant of the payoff, and shows that the exercise region is an interval at the bottom of the price range.
--
--   **Formalization Note** $P$ is `perpetualPut`; stopping times are with respect to the filtration of the moves and take values in $\mathbb N_0\cup\{\infty\}$; expectations are lower Lebesgue integrals. $J_n$ is the $n$-fold iterate of `putT` applied to $(K-x)^+$; $J_{f^*}$ is `exerciseValue` of $E^*$; $\tau^*$ is `policyTime` of the stationary rule $E^*$. Optimality of $\tau^*$ means that its expected payoff equals the supremum over all stopping times.
--
--   Differences from the source:
--   - reading: strike K (sign not stated) → hypothesis 0 < K; reason: a strike price is positive; at K = 0 part e) fails (P ≡ 0, E* = ℝ₊)
--   - reading: P(x) := sup_τ E[β^τ (K − S_τ)] (p.337) → payoff (K − S_τ)⁺ in perpetualPut; reason: the book's own reading (p.332 'we can equivalently choose h⁺', first display of the proof, p.338); both suprema are equal
--   - encoding: stopping times of the natural filtration of (X_n) → IsStoppingTime: {τ = n} determined by the first n moves, values in ℕ∞; reason: same filtration for x > 0; at the absorbing price x = 0 both give P(0) = K
--   - generalization: c): P is smallest among (measurable) superharmonic majorants → P ≤ v for every function v : ℝ → ℝ satisfying the two inequalities on E, measurable or not; reason: a larger class of competitors; it contains the book's, so the claim specializes to it
--   - encoding: c): functions with values in [0, ∞] → real-valued v; reason: if v solves the inequalities so does min(v, K), which is real and ≤ v
--   - encoding: J_{f*} := lim T^n_{f*} 0 → limUnder atTop of n ↦ (T_{f*}^n 0)(x); reason: the sequence is increasing and bounded by K on E, so limUnder is its limit
--   - correction: e) holds for every binomial market with d < 1 + i < u → e) under the extra hypothesis d < 1; reason: for i = 1/2, u = 2, d = 1 (allowed, p.60) the price never falls, P(x) = (K − x)⁺ for all x ≥ 0 and E* = ℝ₊ is not {x ≤ x*} with x* ≤ K
--   - reading: e) 'i.e. it is optimal to exercise the perpetual put option the first time the stock falls below x*' → not a separate clause: with E* = [0, x*] it is the τ* of d), optimal under d)'s hypothesis; reason: read unconditionally it is false at β = 1, where P ≡ K on (0, ∞) is attained by no stopping time
--   - encoding: 𝔼^ℚ_x and sup_τ as real numbers, on the probability space of the market → lower Lebesgue integrals in ℝ≥0∞ on the coin space ℕ → Bool under the product law pathLaw; P is toReal of the ℝ≥0∞ supremum; reason: the integrand is nonnegative and bounded by K on E, so the supremum is finite and the values agree
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, Theorem 11.1.3, pp.337–338, PDF 345–346

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_putT
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_exerciseValue
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_policyTime
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_exerciseRegion

open MeasureTheory Filter Topology
open scoped ENNReal
open FinancialDerivatives.FD04 (putPayoff)

namespace BauerleRiederMDP.AmericanPut

/-- **Theorem 11.1.3** (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011),
pp.337–338, PDF 345–346), the perpetual American put in the binomial model with `d < 1 + i < u`, strike `K`,
`P(x) := sup_{τ ≤ ∞} 𝔼^ℚ_x[β^τ (K − S_τ)]` (reward `0` on `{τ = ∞}`), `E = ℝ₊`:
a) for `x > 0`, `P(x) = J(x) = lim_{n→∞} J_n(x)`, where `J₀ = (K − x)⁺`, `J_n = 𝒯J_{n−1}`;
b) `P = 𝒯P` with `𝒯P(x) = max{(K − x)⁺, β(qP(xu) + (1 − q)P(xd))}`, and `0 ≤ P(x) ≤ K` for `x ∈ E`;
c) `P` is the smallest function on `E` with `P(x) ≥ (K − x)⁺` and `P(x) ≥ β(qP(xu) + (1 − q)P(xd))`;
d) with `E* := {x ∈ E | P(x) = (K − x)⁺}`, `f* = 1_{E*}` and `J_{f*} := lim_{n→∞} 𝒯^n_{f*} 0`: if
`J_{f*} ≥ 𝒯J_{f*}` then `P = J_{f*}` on `E` and `τ* := inf{n ∈ ℕ₀ | X_n ∈ E*}` is an optimal exercise time;
e) (corrected: `d < 1`) there is `x* ∈ [0, K]` with `E* = {x ∈ E | x ≤ x*}`.

**Formalization Note.** The strike is positive (`0 < K`, the standing meaning of a strike price). `P` is
`perpetualPut` (payoff `(K − S_τ)⁺`, stopping times with values in `ℕ₀ ∪ {∞}`, `ℚ = pathLaw`); `J_n` is
`(putT M K)^[n] (putPayoff K)`; `J_{f*}` is `exerciseValue` for the set `E*`; `τ*` is `policyTime` of the
stationary rule `E*`, and "optimal" means that its expected payoff equals the supremum over all stopping times.
Part e) is false as printed when `d ≥ 1` (allowed by the book when `i > 0`): then the price never falls, `P(x) =
(K − x)⁺` for all `x ≥ 0` and `E* = ℝ₊`; the hypothesis `d < 1` is added to e) only. -/
theorem theorem_11_1_3 (M : BinomialMarket) (K : ℝ) (hK : 0 < K) :
    -- a)
    (∀ x : ℝ, 0 < x →
      Tendsto (fun n : ℕ => ((M.putT K)^[n] (putPayoff K)) x) atTop (𝓝 (M.perpetualPut K x))) ∧
    -- b)
    ((∀ x : ℝ, 0 ≤ x → M.perpetualPut K x = M.putT K (M.perpetualPut K) x) ∧
      ∀ x : ℝ, 0 ≤ x → 0 ≤ M.perpetualPut K x ∧ M.perpetualPut K x ≤ K) ∧
    -- c)
    ((∀ x : ℝ, 0 ≤ x → putPayoff K x ≤ M.perpetualPut K x ∧
        M.beta * (M.q * M.perpetualPut K (x * M.u) + (1 - M.q) * M.perpetualPut K (x * M.d)) ≤
          M.perpetualPut K x) ∧
      ∀ v : ℝ → ℝ, (∀ x : ℝ, 0 ≤ x → putPayoff K x ≤ v x ∧
          M.beta * (M.q * v (x * M.u) + (1 - M.q) * v (x * M.d)) ≤ v x) →
        ∀ x : ℝ, 0 ≤ x → M.perpetualPut K x ≤ v x) ∧
    -- d)
    ((∀ x : ℝ, 0 ≤ x → M.putT K (M.exerciseValue K (M.exerciseRegion K)) x ≤
        M.exerciseValue K (M.exerciseRegion K) x) →
      ∀ x : ℝ, 0 ≤ x → M.perpetualPut K x = M.exerciseValue K (M.exerciseRegion K) x ∧
        IsStoppingTime (M.policyTime x (fun _ => M.exerciseRegion K)) ∧
        M.putReward K x (M.policyTime x (fun _ => M.exerciseRegion K)) =
          ⨆ τ : {τ : (ℕ → Bool) → ℕ∞ // IsStoppingTime τ}, M.putReward K x τ.1) ∧
    -- e) (corrected: `d < 1`)
    (M.d < 1 → ∃ xstar ∈ Set.Icc (0 : ℝ) K,
      M.exerciseRegion K = {x : ℝ | 0 ≤ x ∧ x ≤ xstar}) := by sorry

end BauerleRiederMDP.AmericanPut
