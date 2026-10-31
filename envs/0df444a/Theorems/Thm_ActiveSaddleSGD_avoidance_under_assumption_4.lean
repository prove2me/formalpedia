-- Prove2me | Theorems.Thm_ActiveSaddleSGD_avoidance_under_assumption_4
-- name    : ActiveSaddleSGD.avoidance_under_assumption_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:49.381302+00:00
-- url     : https://prove2.me/theorems/85372651-9301-4024-a2e8-fb0e5e8f64c3
-- title:
--   §6.2.5 — Theorem 3 under Assumption 4: $\mathbb P(y_n^N\to x^*)=0$ and $\mathbb P(x_n\to x^*)=0$ (corrected: $D$ extends from the ball of radius $2r$)
-- statement:
--   Let Assumptions 1, 2 and 4 hold. Then
--   $$
--   \mathbb P(x_n\to x^*)=0,
--   $$
--   and for $r$ small, for each field $D$ and each $N$, also $\mathbb P(y_n^N\to x^*)=0$.
--
--   The statement combines Proposition 3 with the results of §6.2. Theorem 3 follows by the reduction of p.18 from Assumption 3 to Assumption 4.
--
--   Differences from the source:
--   - correction: $D$ is a bounded continuous extension of $\nabla(F\circ P_M)$ from $B(0,r)$ → $D$ agrees with $\nabla(F\circ P_M)$ on the closed ball of radius $2r$; reason: if $M$ is curved, a point $x$ with $\|x\|\le r$ can have $\|P_M(x)\|>r$; take $D$ continuous with $\|D(y)-\nabla(F\circ P_M)(y)\|\asymp\mathrm{dist}(y,B(0,r))^{1/2}$ outside the ball; at such $y=y_n^N$ the printed bounds, of size $\|z_n^N\|+\gamma_n$, cannot absorb that error, while $P_M(B(0,r))\subset B(0,2r)$ because $0\in M$
--   - encoding: $N\ge0$ → $N\ge1$; reason: $\gamma_{N-1}$ is undefined at $N=0$ and the events $\mathcal A_N$ increase, so nothing is lost
--   - encoding: "$r$ fixed, adjusted in the course of the proof" → $\exists r_1>0,\ \forall r\in(0,r_1)$; reason: that is what p.18 and "for $r$ small enough" say
--   - encoding: the proofs set $x^*=0$ → general $x^*$, with balls around $x^*$; reason: translation; same instances
--   - encoding: $P_M$ on a ball → a total map $P$ with `IsProjectionOn`; reason: only its values on the ball are constrained; same instances
--   - reading: "Almost surely, … there is $A,B>0$" in Assumption 4 → deterministic $A,B>0$, chosen before "almost surely"; reason: Proposition 4 iii) and Lemma 4 give a deterministic $C$, which a random bound $B$ would not, and the proof of Lemma 4 (p.21) bounds $\mathbb E_n\|\eta_{n+1}\|^4$ by a constant
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, §6.2.5, p.23, "As a consequence, we obtain", with (15), p.18

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ActiveSaddleSGD_ManifoldCalculus
import Definitions.Def_ActiveSaddleSGD_ActiveManifold
import Definitions.Def_ActiveSaddleSGD_Algorithm
import Definitions.Def_ActiveSaddleSGD_Noise
import Definitions.Def_ActiveSaddleSGD_ProjectedIterates

open ProjLikeRetr.Retractor MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace ActiveSaddleSGD

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, §6.2.5, p.23, with (15), p.18: under Assumptions
1, 2 and 4, `ℙ(y_n^N → x*) = 0` for every `N`, and `ℙ(x_n → x*) = 0`.

**Formalization Note** `ℙ(x_n → x*) = 0` is stated first, on its own: it needs no `P`. The clause on
`y^N` is for `r` small, each `D` of `IsProjectedField` and `N ≥ 1` (see `projIter`). `x*` is general
where the page has `0`. -/
theorem avoidance_under_assumption_4 {d k : ℕ} {f F : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {M U : Set (EuclideanSpace ℝ (Fin d))} {xs w : EuclideanSpace ℝ (Fin d)} {Cv β : ℝ}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {x v η : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {γ : ℕ → ℝ} {c₁ c₂ α : ℝ}
    (hA1 : Assumption1 f ℱ x v η γ c₁ c₂ α)
    (hA2 : Assumption2 k f F G M U xs w Cv β)
    (hA4 : Assumption4 μ ℱ η (negEigenspace (curvOp M G xs))) :
    μ {ω | Tendsto (fun n => x n ω) atTop (𝓝 xs)} = 0 ∧
      ∀ (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (r₀ : ℝ), 0 < r₀ →
        IsProjectionOn M P xs r₀ →
        ∃ r₁ > 0, ∀ r, 0 < r → r < r₁ →
          ∀ D : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
            IsProjectedField F P D xs r → ∀ N : ℕ, 1 ≤ N →
              μ {ω | Tendsto (fun n => projIter x η γ xs P D r N n ω) atTop (𝓝 xs)} = 0 := by sorry

end ActiveSaddleSGD
