-- Prove2me | Theorems.Thm_ActiveSaddleSGD_proposition_5
-- name    : ActiveSaddleSGD.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:59.648993+00:00
-- url     : https://prove2.me/theorems/b163fa6f-e48f-45a0-b6bb-657ade5c81e7
-- title:
--   Proposition 5 — $\chi_n^{-1/2}\sum_{i\ge n}\gamma_i\mathbb E_n\|z_i^N\|\to0$ almost surely
-- statement:
--   Let Assumptions 1, 2 and 4 hold. Then, for $r$ small enough, the sequence $(z_n^N)$ satisfies
--   $$
--   \chi_n^{-1/2}\sum_{i=n}^\infty\gamma_i\mathbb E_n\|z_i^N\|\xrightarrow[n\to\infty]{\text{a.s.}}0,\qquad\chi_n=\sum_{i\ge n}\gamma_i^2.
--   $$
--
--   This is the last requirement of Proposition 3 on the perturbation $\tilde\varrho$.
--
--   **Formalization Note** $z_n^N$ is `projResidual`, for any $N$; it does not depend on $D$. The sum and the conditional expectations are in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: $z_n^N=(x_n-y_n^N)\mathbb 1_{n<\tau_N}$ → `projResidual`, $(x_n-P(x_n))\mathbb 1_{n<\tau_N}$; reason: on $[n<\tau_N]$, $n\ge N$, the page has $y_n^N=P_M(x_n)$; same process, and it needs no $D$
--   - encoding: "$r$ fixed, adjusted in the course of the proof" → $\exists r_1>0,\ \forall r\in(0,r_1)$; reason: that is what p.18 and "for $r$ small enough" say
--   - encoding: the proofs set $x^*=0$ → general $x^*$, with balls around $x^*$; reason: translation; same instances
--   - encoding: $P_M$ on a ball → a total map $P$ with `IsProjectionOn`; reason: only its values on the ball are constrained; same instances
--   - reading: "Almost surely, … there is $A,B>0$" in Assumption 4 → deterministic $A,B>0$, chosen before "almost surely"; reason: Proposition 4 iii) and Lemma 4 give a deterministic $C$, which a random bound $B$ would not, and the proof of Lemma 4 (p.21) bounds $\mathbb E_n\|\eta_{n+1}\|^4$ by a constant
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, Proposition 5, p.23

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

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Proposition 5, p.23: under Assumptions 1, 2 and
4, `χ_n^{-1/2} Σ_{i=n}^∞ γ_i E_n‖z_i^N‖ → 0` almost surely, where `χ_n = Σ_{i≥n} γ_i²`.

**Formalization Note** The sum and the conditional expectations are in `ℝ≥0∞`, so a divergent sum
is `⊤` and not a junk `0`. `χ_n` is finite because `α > 1/2`, and positive because `γ_n > 0`. `r` is
small, as in Lemmas 4 and 5, on which the proof rests. -/
theorem proposition_5 {d k : ℕ} {f F : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {M U : Set (EuclideanSpace ℝ (Fin d))} {xs w : EuclideanSpace ℝ (Fin d)} {Cv β : ℝ}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {x v η : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {γ : ℕ → ℝ} {c₁ c₂ α : ℝ}
    (hA1 : Assumption1 f ℱ x v η γ c₁ c₂ α)
    (hA2 : Assumption2 k f F G M U xs w Cv β)
    (hA4 : Assumption4 μ ℱ η (negEigenspace (curvOp M G xs)))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hP : IsProjectionOn M P xs r₀) :
    ∃ r₁ > 0, ∀ r, 0 < r → r < r₁ → ∀ N : ℕ,
      ∀ᵐ ω ∂μ, Tendsto
        (fun n => ENNReal.ofReal (tailChi γ n ^ (-(1 / 2) : ℝ)) *
          ∑' i, ENNReal.ofReal (γ (n + i)) *
            condLExp (ℱ n) μ (fun a => ‖projResidual x xs P r N (n + i) a‖ₑ) ω)
        atTop (𝓝 0) := by sorry

end ActiveSaddleSGD
