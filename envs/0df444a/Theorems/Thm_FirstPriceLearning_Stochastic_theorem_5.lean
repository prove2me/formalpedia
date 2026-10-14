-- Prove2me | Theorems.Thm_FirstPriceLearning_Stochastic_theorem_5
-- name    : FirstPriceLearning.Stochastic.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:58.86883+00:00
-- url     : https://prove2.me/theorems/48e89a5d-bf2a-4b3e-896f-1ba9c0aa76f5
-- title:
--   Theorem 5 (iid contexts), p. 18 — Algorithm 3 has 𝔼[R_T] ≤ 1 + 24√(αβT log(2T) log(2MKT²) log(2MKT³))(1 + log T)
-- statement:
--   Consider any partially ordered contextual bandit (Definition 3) with $M,K\ge1$ contexts and actions, rewards in $[0,1]$, and let $\alpha$ and $\beta$ bound the independence numbers of the feedback graph $G$ and of the context order $(\mathcal C,\preceq_{\mathcal C})$. Let the contexts $c_1,\dots,c_T$ ($T\ge1$) be iid from an arbitrary distribution $F$ on $\mathcal C$, independent of the reward vectors and of the algorithm's internal randomness. Then Algorithm 3 with $\delta=1/(2T)$ (and any topological ordering of the contexts) satisfies
--
--   $$
--   \mathbb E[R_T(\pi)]\ \le\ 1+24\sqrt{\alpha\beta T\log(2T)\log(2MKT^2)\log(2MKT^3)}\,\big(1+\log T\big),
--   $$
--
--   with $R_T$ the regret (5) and the expectation over the contexts, the rewards and the algorithm's randomness. In particular the regret is $\tilde O(\sqrt{\alpha\beta T})$, essentially independent of $M$ and $K$.
--
--   **Formalization Note.** The conclusion also asserts that the regret is integrable, so the expectation is a genuine one. The factor $(1+\log T)$ is outside the square root, as printed. The adversarial-context part of the theorem is not stated in this mission.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 18, Theorem 5 (first part, i.i.d. contexts)

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Algorithm3

namespace FirstPriceLearning.Stochastic

open MeasureTheory

/-- Theorem 5, stochastic part (p. 18): on a partially ordered contextual bandit (Definition 3)
whose feedback graph and context order have independence numbers at most `α` and `β`, with iid
contexts of law `F` independent of the iid reward vectors and of the algorithm's uniforms,
Algorithm 3 with `δ = 1/(2T)` satisfies
`𝔼[R_T(π)] ≤ 1 + 24 √(αβT log(2T) log(2MKT²) log(2MKT³)) (1 + log T)`. The regret is integrable
(so the expectation is a genuine one). -/
theorem theorem_5 (M K T : ℕ) (hM : 0 < M) (hK : 0 < K) (hT : 1 ≤ T) (B : ContextualBandit M K)
    (leC : Fin M → Fin M → Prop) (hB : IsPartiallyOrdered B leC) (α β : ℕ)
    (hα : IndepNumberLe B.E α) (hβ : OrderIndepNumberLe leC β) (ord : Fin M ≃ Fin M)
    (hord : IsTopoOrder leC ord) (F : Measure (Fin M)) [IsProbabilityMeasure F] :
    let p : Alg3Params M K := ⟨T, 1 / (2 * T), B.E, leC, ord, hK⟩
    let μ := (Measure.pi fun _ : Fin T => F).prod
      ((Measure.pi fun _ : Fin T => B.P).prod
        (Measure.pi fun _ : Fin T => (volume : Measure unitInterval)))
    let R := fun ω : (Fin T → Fin M) × (Fin T → Fin M → Fin K → ℝ) × (Fin T → unitInterval) =>
      B.regret ω.1 (Alg3.actions p ω.1 ω.2.1 ω.2.2)
    Integrable R μ ∧
      ∫ ω, R ω ∂μ ≤
        1 + 24 * Real.sqrt (α * β * T * Real.log (2 * T) * Real.log (2 * M * K * (T : ℝ) ^ 2) *
          Real.log (2 * M * K * (T : ℝ) ^ 3)) * (1 + Real.log T) := by sorry

end FirstPriceLearning.Stochastic
