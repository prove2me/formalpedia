-- Prove2me | Theorems.Thm_CasinoCPT_Embedding_theorem_3_1
-- name    : CasinoCPT.Embedding.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:38.585913+00:00
-- url     : https://prove2.me/theorems/36df5134-fd93-4e1a-bd00-b5ecb4b27f79
-- title:
--   Theorem 3.1, p. 16 — µ ∈ 𝒫₀(ℤ) on [−T, T] is the law of S_τ for some τ ∈ 𝒯_T iff (8); then a randomized Root time embeds µ
-- statement:
--   Let $S$ be a standard symmetric random walk on a filtered probability space $(\Omega,\mathcal F,P;(\mathcal F_t))$ whose $\mathcal F_0$ carries a uniform random variable on $[0,1]$. Let $T\ge1$ and let $\mu\in\mathcal P_0(\mathbb Z)$ be a centred law with $\mu([-T,T])=1$. Then there exists a stopping time $\tau\in\mathcal T_T$ such that $S_\tau\sim\mu$ if and only if
--   $$U_\mu(x)\le\frac{U^\mu_{T-1}(x+1)+U^\mu_{T-1}(x-1)}{2},\qquad x=-(T-2),-(T-4),\dots,T-4,T-2.\tag{8}$$
--   Moreover, in this case there exists a randomized Root stopping time $\tau_R(b,r)\in\mathcal T_T$ such that $S_{\tau_R(b,r)}\sim\mu$.
--
--   Here $U_\mu$ is the potential of $\mu$, $U^\mu_t$ are the evolutional functions (6), and $\mathcal T_T$ is the set of all stopping times bounded by $T$, path-dependent and randomized ones included. The theorem identifies the set of laws a gambler can realise by leaving the casino before time $T$. This turns the gambler's optimal stopping problem into an optimisation over laws subject to the explicit constraints (8), and it shows that randomized Root stopping times suffice.
--
--   **Formalization Note.** The statement quantifies over every casino space and every stopping time on it. The "moreover" clause asserts a barrier $b$, boundary probabilities $r$ and a family of independent $\mathcal F_0$-measurable coins with the laws of (7), whose Root time lies in $\mathcal T_T$ (an $(\mathcal F_t)$-stopping time with $\tau_R\le T$ everywhere) and embeds $\mu$. It does not assert that every such coin family gives $\tau_R\le T$ at every sample point: a coin of probability one may be altered on a null set, which can only change $\tau_R$ on a null set. The index set of (8) is the set of integers $x$ with $|x|\le T-2$ and $x+T$ even; it is empty for $T=1$.
-- source:
--   Hu, Obłój & Zhou, When to Quit Gambling, if You Must!, arXiv:2102.03157v1, p. 16, Theorem 3.1

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model

namespace CasinoCPT.Embedding

open MeasureTheory ProbabilityTheory

/-- Theorem 3.1, p. 16: let `T ≥ 1` and `μ ∈ 𝒫₀(ℤ)` with `μ([-T, T]) = 1`. There is a stopping
time `τ ∈ 𝒯_T` with `S_τ ∼ μ` if and only if condition (8) holds. Moreover, in this case there
is a randomized Root stopping time `τ_R(b, r) ∈ 𝒯_T` with `S_{τ_R(b, r)} ∼ μ`. -/
theorem theorem_3_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (S : ℕ → Ω → ℤ) (ξ : Ω → ℝ) (hS : IsCasinoSpace P F S ξ)
    (T : ℕ) (hT : 1 ≤ T) (μ : Measure ℤ) (hμ : InP0Z μ)
    (hsupp : μ (Set.Icc (-(T : ℤ)) T) = 1) :
    ((∃ τ : Ω → ℕ∞, IsAdmissible F T τ ∧ P.map (stoppedValue S τ) = μ) ↔ Cond8 μ T) ∧
      (Cond8 μ T → ∃ (b : ℤ → ℕ) (r : ℤ → ℝ) (coin : ℕ → ℤ → Ω → Bool),
        IsRootBarrier b r ∧ IsRootCoins P F b r coin ∧
          IsAdmissible F T (rootTime S b coin) ∧
          P.map (stoppedValue S (rootTime S b coin)) = μ) := by sorry

end CasinoCPT.Embedding
