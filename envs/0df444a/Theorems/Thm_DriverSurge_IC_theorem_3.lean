-- Prove2me | Theorems.Thm_DriverSurge_IC_theorem_3
-- name    : DriverSurge.IC.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:27.222961+00:00
-- url     : https://prove2.me/theorems/17e9941d-8bd1-4e53-89a6-a8b640c1dafd
-- title:
--   Theorem 3, p. 13 (corrected: 0 ≤ R2) — prices m_iτ + z_iq_{i→j}(τ) meeting targets R1 < R2 make {(0, t1), (0, ∞)} optimal, and accept-all uniquely optimal for R1/R2 ∈ (C, 1)
-- statement:
--   Consider the dynamic model with request rates $\lambda_1,\lambda_2>0$, switching rates $\lambda_{1\to2},\lambda_{2\to1}>0$ and trip-length laws $F_1,F_2$ on $(0,\infty)$ with bounded densities and finite means. A driver's **earnings rate** under prices $w=\{w_1,w_2\}$ and a policy $\sigma=\{\sigma_1,\sigma_2\}$ (open sets $\sigma_i\subseteq(0,\infty)$ of accepted trip lengths) is $R(w,\sigma)=\liminf_{t\to\infty}R(w,\sigma,t)/t$, where $R(w,\sigma,t)$ is the pay of the trips accepted by time $t$ and a trip started in state $i$ with length $\tau$ pays $w_i(\tau)$. Let
--   $$C=1-\frac{1}{\bar T_1}\cdot\frac{\bar Q_2(\lambda_{1\to2}\bar T_1-\bar Q_1)+\bar Q_1(\bar T_2\lambda_{1\to2}+\bar Q_2)}{\bar Q_2(\lambda_{1\to2}\bar T_1-\bar Q_1)+\lambda_{1\to2}(\bar T_2\lambda_{1\to2}+\bar Q_2)},$$
--   where $\bar T_i=1+\lambda_i\int\tau\,dF_i$ and $\bar Q_i=\lambda_{i\to j}+\lambda_i\int q_{i\to j}\,dF_i$ are taken at accept-all. Then:
--
--   1. $C\in[0,1)$.
--   2. For all targets $R_1<R_2$ with $R_2\ge0$ there are prices of the form
--   $$w_i(\tau)=m_i\tau+z_i\,q_{i\to j}(\tau),\qquad m_1,m_2,z_2\ge0,$$
--   meeting the targets $R_i(w_i,(0,\infty))=R_i$, and $t_1\in[0,\infty]$, such that the policy $\{(0,t_1),(0,\infty)\}$ (accept every trip in the surge state and all trips shorter than $t_1$ in the non-surge state) is optimal: almost surely its earnings rate is at least that of every policy.
--   3. If $R_1/R_2\in(C,1)$, there are such prices meeting the targets that are **fully incentive compatible**: almost surely, accepting every request earns at least as much as every policy, and strictly more than every policy that rejects a set of trip lengths of positive $F_1$- or $F_2$-measure. Accepting all requests is thus the unique optimal policy up to differences of measure zero.
--
--   The prices and $t_1$ are fixed before the probability space, the initial world state and the competing policy. This is the paper's main result: incentive-compatible surge pricing exists exactly when the non-surge target is not too far below the surge target.
--
--   **Formalization Note** Lean state `0` is the paper's non-surge state 1 and Lean state `1` the surge state 2; `other i` is the state $j\ne i$. The earnings rate is the `EReal` liminf of the pathwise model `Def_DriverSurge_IC_Process`; the statement holds for every probability space carrying that model and every initial world state. $R_i(w_i,(0,\infty))$ is $W_i/T_i$ at accept-all.
--
--   Differences from the source:
--   - correction: "Let $R_1<R_2$ be target earning rates" (any reals) → $0\le R_2$ in clause 2; reason: with $m_2,z_2\ge0$ the surge price is nonnegative on $(0,\infty)$, so $R_2(w_2,(0,\infty))\ge0$ and e.g. the targets $R_1=-2$, $R_2=-1$ cannot be met, for any primitives
--   - encoding: $R_1/R_2\in(C,1)$ → $0<R_2$ stated in clause 3; reason: implied: $C\ge0$ and $R_1/R_2\in(C,1)$ with $R_1<R_2$ force $R_2>0$; with $R_2=0$ Lean's $R_1/0=0\notin(C,1)$ anyway
--   - encoding: D.3.1's standing assumption "$F_i$ continuous, i.e., $f_i$ bounded" → a bounded measurable density as a hypothesis; reason: the paper's standing assumption for all of App. D, stated once
--   - encoding: $C$ uses $\bar T_i=\lambda_iF_i((0,\infty))T_i((0,\infty))$, implicitly finite → finite mean trip lengths assumed; reason: $C$ is undefined otherwise; only undefined cases are excluded
--   - reading: "the optimal driver policy is to accept every trip in the surge state and all trips up to a certain length in the non-surge state" → $\{(0,t_1),(0,\infty)\}$ is optimal (uniqueness not claimed); reason: uniqueness is claimed only for the fully incentive-compatible prices; the proof (p. 61) derives optimality from Theorem 4
--   - reading: "fully incentive compatible prices of this form" → prices with $m_1,m_2,z_2\ge0$ meeting the targets $R_i(w_i,(0,\infty))=R_i$; reason: "this form" refers to the first sentence; the targets are the paper's constraints (§2.3, p. 8; proof p. 61)
--   - encoding: "the unique optimal driver policy (up to differences of measure 0)" → strictly larger earnings rate, almost surely, than every policy rejecting a set of positive $F_1$- or $F_2$-measure; reason: a policy differing from accept-all on an $F_i$-null set is the same policy up to measure 0; every other policy is strictly worse
--   - encoding: $R(w,\sigma)$, "a deterministic (non-random) quantity" (p. 6) → compared almost surely, for each competing policy, on every probability space carrying the pathwise model and from every initial world state; reason: the liminf is almost surely constant (Lemma 1), so the almost-sure comparison is the comparison of the deterministic values; no instance of the model is excluded
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, p. 13, Theorem 3 (proof pp. 60–61)

import Mathlib
import Definitions.Def_DriverSurge_IC_Process
import Definitions.Def_DriverSurge_IC_Pricing

namespace DriverSurge.IC

open MeasureTheory Set

/-- Theorem 3 (Garg–Nazerzadeh, p. 13; corrected: `0 ≤ R₂` in the second clause). Lean state `0` is
the paper's non-surge state 1 and Lean `1` the surge state 2. Under the standing assumptions (bounded
densities) and finite mean trip lengths:
1. `C ∈ [0, 1)`;
2. for all targets `R₁ < R₂` with `R₂ ≥ 0` there are prices `w_i(τ) = m_iτ + z_iq_{i→j}(τ)` with
   `m_1, m_2, z_2 ≥ 0` meeting the targets `R_i(w_i, (0, ∞)) = R_i`, and a threshold `t₁ ∈ [0, ∞]`, such
   that on every probability space carrying the model, from every initial world state, the policy
   `{(0, t₁), (0, ∞)}` earns almost surely at least as much as every policy;
3. if moreover `R₁/R₂ ∈ (C, 1)`, there are such prices for which accepting every request earns almost
   surely at least as much as every policy, and strictly more than every policy that rejects a set of
   trip lengths of positive `F_1`- or `F_2`-measure. -/
theorem theorem_3 (P : Primitives) (f : Fin 2 → ℝ → ℝ) (hf : HasBoundedDensity P f)
    (hmean : FiniteMean P) :
    (0 ≤ Cconst P ∧ Cconst P < 1) ∧
    (∀ R₁ R₂ : ℝ, R₁ < R₂ → 0 ≤ R₂ →
      ∃ m z : Fin 2 → ℝ, 0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1 ∧
        stateRate P 0 (price P m z 0) (Ioi 0) = R₁ ∧ stateRate P 1 (price P m z 1) (Ioi 0) = R₂ ∧
        ∃ t₁ : EReal, 0 ≤ t₁ ∧
          ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (i₀ : Fin 2) (X : Ω → Path),
            IsDriverModel P μ i₀ X → ∀ σ : Fin 2 → Set ℝ, IsPolicy σ →
              ∀ᵐ ω ∂μ, earningsRate (price P m z) σ i₀ (X ω) ≤
                earningsRate (price P m z) (lowerThenAll t₁) i₀ (X ω)) ∧
    (∀ R₁ R₂ : ℝ, R₁ < R₂ → 0 < R₂ → Cconst P < R₁ / R₂ → R₁ / R₂ < 1 →
      ∃ m z : Fin 2 → ℝ, 0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1 ∧
        stateRate P 0 (price P m z 0) (Ioi 0) = R₁ ∧ stateRate P 1 (price P m z 1) (Ioi 0) = R₂ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (i₀ : Fin 2) (X : Ω → Path),
          IsDriverModel P μ i₀ X → ∀ σ : Fin 2 → Set ℝ, IsPolicy σ →
            (∀ᵐ ω ∂μ, earningsRate (price P m z) σ i₀ (X ω) ≤
              earningsRate (price P m z) acceptAll i₀ (X ω)) ∧
            ((P.F 0 (Ioi 0 \ σ 0) ≠ 0 ∨ P.F 1 (Ioi 0 \ σ 1) ≠ 0) →
              ∀ᵐ ω ∂μ, earningsRate (price P m z) σ i₀ (X ω) <
                earningsRate (price P m z) acceptAll i₀ (X ω))) := by sorry

end DriverSurge.IC
