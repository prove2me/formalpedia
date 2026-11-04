-- Prove2me | Theorems.Thm_CasinoCPT_Embedding_proposition_A_3_i_imp_ii
-- name    : CasinoCPT.Embedding.proposition_A_3_i_imp_ii
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-03T07:08:40.176201+00:00
-- url     : https://prove2.me/theorems/145c7842-b70b-4635-b791-982bccde4139
-- title:
--   Proposition A.3, (i) ⇒ (ii), pp. 46–48 — if U^µ_T = U_µ on ℤ, a randomized Root time τ_R ≤ T has U_{S_{τR∧t}} = U^µ_t and embeds µ
-- statement:
--   Let $S$ be a standard symmetric random walk on a filtered probability space $(\Omega,\mathcal F,P;(\mathcal F_t))$ whose $\mathcal F_0$ carries a uniform random variable on $[0,1]$ (a casino space). Let $T\ge1$ and let $\mu\in\mathcal P_0(\mathbb Z)$ be a centred law with $\mu([-T,T])=1$, with potential $U_\mu$ and evolutional functions $U_t=U^\mu_t$ from (6). Suppose
--   $$U_T(x)=U_\mu(x)\qquad\forall x\in\mathbb Z .$$
--   Then there exist a Root barrier $b$ with boundary probabilities $r$ and a family of independent $\mathcal F_0$-measurable coins $\{\xi_{t,x}\}$ with the laws (7)/(20) such that the randomized Root stopping time
--   $$\tau_R(b,r)=\inf\{t\in\mathbb N: t\ge b(S_t),\ \xi_{t,S_t}=0\}$$
--   is an $(\mathcal F_t)$-stopping time with $\tau_R\le T$ everywhere, its stopped potentials satisfy
--   $$U_{S_{\tau_R\wedge t}}(x)=U_t(x)\qquad\forall x\in\mathbb Z,\ t\le T,$$
--   and in particular $S_{\tau_R}\sim\mu$.
--
--   This is the implication (i) $\Rightarrow$ (ii) of Proposition A.3. In the paper the barrier is $b(x)=\inf\{t\ge|x|:U_{t+1}(x)=U_\mu(x)\}$ (19) and the boundary probability is $r(x)=\dfrac{U_t(x-1)+U_t(x+1)-2U_\mu(x)}{U_t(x-1)+U_t(x+1)-2U_t(x)}$ at $t=b(x)$ (20); the formal statement only asserts existence.
-- source:
--   Hu, Obłój & Zhou, When to Quit Gambling, if You Must!, arXiv:2102.03157v1, pp. 46–48, Proposition A.3, proof of (i) → (ii), eqs. (19)–(20)

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model

namespace CasinoCPT.Embedding

open MeasureTheory ProbabilityTheory

/-- Proposition A.3, (i) ⇒ (ii), pp. 46–48: let `T ≥ 1` and `μ ∈ 𝒫₀(ℤ)` with `μ([-T, T]) = 1`.
If `U^μ_T(x) = U_μ(x)` for all `x ∈ ℤ`, then there is a randomized Root stopping time
`τ_R(b, r) ≤ T` with `U_{S_{τ_R ∧ t}} = U^μ_t` on the integers for all `t ≤ T`; in particular
`S_{τ_R} ∼ μ`. -/
theorem proposition_A_3_i_imp_ii {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (S : ℕ → Ω → ℤ) (ξ : Ω → ℝ) (hS : IsCasinoSpace P F S ξ)
    (T : ℕ) (hT : 1 ≤ T) (μ : Measure ℤ) (hμ : InP0Z μ)
    (hsupp : μ (Set.Icc (-(T : ℤ)) T) = 1)
    (hi : ∀ x : ℤ, evol μ T x = potential μ (x : ℝ)) :
    ∃ (b : ℤ → ℕ) (r : ℤ → ℝ) (coin : ℕ → ℤ → Ω → Bool),
      IsRootBarrier b r ∧ IsRootCoins P F b r coin ∧
        IsStoppingTime F (rootTime S b coin) ∧ (∀ ω, rootTime S b coin ω ≤ T) ∧
        (∀ t : ℕ, t ≤ T → ∀ x : ℤ,
          potential (P.map (stoppedValue S (fun ω => min (rootTime S b coin ω) (t : ℕ∞))))
            (x : ℝ) = evol μ t x) ∧
        P.map (stoppedValue S (rootTime S b coin)) = μ := by sorry

end CasinoCPT.Embedding
