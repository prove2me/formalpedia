-- Prove2me | Theorems.Thm_ActiveSaddleSGD_lemma_5
-- name    : ActiveSaddleSGD.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:18.071984+00:00
-- url     : https://prove2.me/theorems/0c486767-a878-43d2-b483-e068dc49d53e
-- title:
--   Lemma 5 — $n^a\|z_n^N\|^2\to0$ almost surely for each $a\in(0,2\alpha-1)$
-- statement:
--   Let Assumptions 1, 2 and 4 hold. For $r$ small enough and for each $a\in(0,2\alpha-1)$,
--   $$
--   n^a\|z_n^N\|^2\xrightarrow[n\to\infty]{}0\quad\text{almost surely.}
--   $$
--
--   This is the rate of convergence of the iterates to the manifold.
--
--   **Formalization Note** $z_n^N$ is `projResidual`, for any $N$; it does not depend on $D$. $\alpha=1$ is included: the phrase "since $\alpha<1$" in the proof needs only $\alpha\le1$.
--
--   Differences from the source:
--   - encoding: $z_n^N=(x_n-y_n^N)\mathbb 1_{n<\tau_N}$ → `projResidual`, $(x_n-P(x_n))\mathbb 1_{n<\tau_N}$; reason: on $[n<\tau_N]$, $n\ge N$, the page has $y_n^N=P_M(x_n)$; same process, and it needs no $D$
--   - encoding: "$r$ fixed, adjusted in the course of the proof" → $\exists r_1>0,\ \forall r\in(0,r_1)$; reason: that is what p.18 and "for $r$ small enough" say
--   - encoding: the proofs set $x^*=0$ → general $x^*$, with balls around $x^*$; reason: translation; same instances
--   - encoding: $P_M$ on a ball → a total map $P$ with `IsProjectionOn`; reason: only its values on the ball are constrained; same instances
--   - reading: "Almost surely, … there is $A,B>0$" in Assumption 4 → deterministic $A,B>0$, chosen before "almost surely"; reason: Proposition 4 iii) and Lemma 4 give a deterministic $C$, which a random bound $B$ would not, and the proof of Lemma 4 (p.21) bounds $\mathbb E_n\|\eta_{n+1}\|^4$ by a constant
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, Lemma 5, p.22

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

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Lemma 5, p.22: under Assumptions 1, 2 and 4, for
each `a ∈ (0, 2α − 1)`, `n^a ‖z_n^N‖² → 0` almost surely.

**Formalization Note** `r` is small, as in the proof (p.22), and does not depend on `a`. `α = 1` is
included: the page's "since `α < 1`" needs only `α ≤ 1`. -/
theorem lemma_5 {d k : ℕ} {f F : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {M U : Set (EuclideanSpace ℝ (Fin d))} {xs w : EuclideanSpace ℝ (Fin d)} {Cv β : ℝ}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {x v η : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {γ : ℕ → ℝ} {c₁ c₂ α : ℝ}
    (hA1 : Assumption1 f ℱ x v η γ c₁ c₂ α)
    (hA2 : Assumption2 k f F G M U xs w Cv β)
    (hA4 : Assumption4 μ ℱ η (negEigenspace (curvOp M G xs)))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hP : IsProjectionOn M P xs r₀) :
    ∃ r₁ > 0, ∀ r, 0 < r → r < r₁ → ∀ N : ℕ, ∀ a : ℝ, 0 < a → a < 2 * α - 1 →
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (n : ℝ) ^ a * ‖projResidual x xs P r N n ω‖ ^ 2)
        atTop (𝓝 0) := by sorry

end ActiveSaddleSGD
