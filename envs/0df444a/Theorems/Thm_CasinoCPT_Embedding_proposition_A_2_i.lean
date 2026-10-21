-- Prove2me | Theorems.Thm_CasinoCPT_Embedding_proposition_A_2_i
-- name    : CasinoCPT.Embedding.proposition_A_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:31.244914+00:00
-- url     : https://prove2.me/theorems/68911493-29df-4060-ac89-d7c0a96772ad
-- title:
--   Proposition A.2 (i), p. 45 — U_0 ≤ U^µ_t ≤ U_µ ∧ U_{S_t} on ℤ
-- statement:
--   Let $\mu\in\mathcal P_0(\mathbb Z)$ and let $U_t=U^\mu_t$ be the evolutional functions (6). Let $S$ be a standard symmetric random walk on a casino space, and write $U_{S_t}$ for the potential of the law of $S_t$. Then for all $x\in\mathbb Z$ and $t\in\mathbb N$,
--   $$U_0(x)\ \le\ U_t(x)\ \le\ U_\mu(x)\wedge U_{S_t}(x).$$
--
--   The evolutional functions are thus squeezed between $|x|$, the target potential, and the potential of the unstopped walk.
-- source:
--   Hu, Obłój & Zhou, When to Quit Gambling, if You Must!, arXiv:2102.03157v1, p. 45, Proposition A.2 (i)

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model

namespace CasinoCPT.Embedding

open MeasureTheory ProbabilityTheory

/-- Proposition A.2 (i), p. 45: for `μ ∈ 𝒫₀(ℤ)` and `U_t = U^μ_t`,
`U_0(x) ≤ U_t(x) ≤ U_μ(x) ∧ U_{S_t}(x)` for all `x ∈ ℤ`, `t ∈ ℕ`, where `U_{S_t}` is the
potential of the law of the random walk at time `t`. -/
theorem proposition_A_2_i (μ : Measure ℤ) (hμ : InP0Z μ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℕ mΩ) (S : ℕ → Ω → ℤ) (ξ : Ω → ℝ)
    (hS : IsCasinoSpace P F S ξ) :
    ∀ (t : ℕ) (x : ℤ), evol μ 0 x ≤ evol μ t x ∧
      evol μ t x ≤ min (potential μ (x : ℝ)) (potential (P.map (S t)) (x : ℝ)) := by sorry

end CasinoCPT.Embedding
