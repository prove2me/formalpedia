-- Prove2me | Theorems.Thm_ActiveSaddleSGD_lemma_4
-- name    : ActiveSaddleSGD.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:34.838749+00:00
-- url     : https://prove2.me/theorems/6ee2243a-b08d-4d54-970f-6a29564b01e9
-- title:
--   Lemma 4 — the drift inequality for $\|z_n^N\|^2$
-- statement:
--   Let Assumptions 1, 2 and 4 hold, with $\beta>0$ the constant of the angle condition. There is $C>0$ such that if $r>0$ is chosen small enough, then for $n\ge N$, almost surely,
--   $$
--   \mathbb E_n\|z_{n+1}^N\|^2\le\|z_n^N\|^2-\gamma_n\beta\|z_n^N\|+C\gamma_n^2.
--   $$
--
--   This is the key inequality of the proof: the angle condition pulls the iterates to $M$ at a linear rate in the distance.
--
--   **Formalization Note** $z_n^N$ is `projResidual`, for any $N$; it does not depend on $D$. $z_{n+1}^N$ is bounded, so the conditional expectation is genuine.
--
--   Differences from the source:
--   - encoding: $z_n^N=(x_n-y_n^N)\mathbb 1_{n<\tau_N}$ → `projResidual`, $(x_n-P(x_n))\mathbb 1_{n<\tau_N}$; reason: on $[n<\tau_N]$, $n\ge N$, the page has $y_n^N=P_M(x_n)$; same process, and it needs no $D$
--   - encoding: "$r$ fixed, adjusted in the course of the proof" → $\exists r_1>0,\ \forall r\in(0,r_1)$; reason: that is what p.18 and "for $r$ small enough" say
--   - encoding: the proofs set $x^*=0$ → general $x^*$, with balls around $x^*$; reason: translation; same instances
--   - encoding: $P_M$ on a ball → a total map $P$ with `IsProjectionOn`; reason: only its values on the ball are constrained; same instances
--   - reading: "Almost surely, … there is $A,B>0$" in Assumption 4 → deterministic $A,B>0$, chosen before "almost surely"; reason: Proposition 4 iii) and Lemma 4 give a deterministic $C$, which a random bound $B$ would not, and the proof of Lemma 4 (p.21) bounds $\mathbb E_n\|\eta_{n+1}\|^4$ by a constant
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, Lemma 4, p.21

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

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Lemma 4, p.21: under Assumptions 1, 2 and 4
there is `C > 0` such that if `r > 0` is chosen small enough, then
`E_n‖z_{n+1}^N‖² ≤ ‖z_n^N‖² − γ_n β ‖z_n^N‖ + C γ_n²`, with `β` the angle constant.

**Formalization Note** `z` is `projResidual`, bounded by `2r` and adapted, so Mathlib's real `condExp`
is a genuine conditional expectation here. It does not depend on `D`, so no `D` appears and `N = 0`
is allowed. `C` comes before `r`, as on the page. The bound holds almost surely, for each `n ≥ N`. -/
theorem lemma_4 {d k : ℕ} {f F : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {M U : Set (EuclideanSpace ℝ (Fin d))} {xs w : EuclideanSpace ℝ (Fin d)} {Cv β : ℝ}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {x v η : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {γ : ℕ → ℝ} {c₁ c₂ α : ℝ}
    (hA1 : Assumption1 f ℱ x v η γ c₁ c₂ α)
    (hA2 : Assumption2 k f F G M U xs w Cv β)
    (hA4 : Assumption4 μ ℱ η (negEigenspace (curvOp M G xs)))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hP : IsProjectionOn M P xs r₀) :
    ∃ C > 0, ∃ r₁ > 0, ∀ r, 0 < r → r < r₁ → ∀ N n : ℕ, N ≤ n →
      ∀ᵐ ω ∂μ,
        (μ[fun a => ‖projResidual x xs P r N (n + 1) a‖ ^ 2 | ℱ n]) ω ≤
          ‖projResidual x xs P r N n ω‖ ^ 2 - γ n * β * ‖projResidual x xs P r N n ω‖
            + C * γ n ^ 2 := by sorry

end ActiveSaddleSGD
