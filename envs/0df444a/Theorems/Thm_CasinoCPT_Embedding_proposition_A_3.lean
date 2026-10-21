-- Prove2me | Theorems.Thm_CasinoCPT_Embedding_proposition_A_3
-- name    : CasinoCPT.Embedding.proposition_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:32.371425+00:00
-- url     : https://prove2.me/theorems/0824cec7-3654-438b-8ae8-dbe3045c3abf
-- title:
--   Proposition A.3, p. 46 — U^µ_T = U_µ ⇔ a Root time ≤ T embeds µ ⇔ some τ ∈ 𝒯_T embeds µ; and U_{S_{τ∧t}} ≤ U^µ_t
-- statement:
--   Let $S$ be a standard symmetric random walk on a casino space, $T\ge1$, and $\mu\in\mathcal P_0(\mathbb Z)$ with $\mu([-T,T])=1$. Let $U_t=U^\mu_t$ be the evolutional functions (6). The following are equivalent:
--
--   1. $U_T(x)=U_\mu(x)$ for all $x\in\mathbb Z$;
--   2. there are a barrier $b$, boundary probabilities $r$ and a family of coins $\{\xi_{t,x}\}$ as in (7) on the casino space, such that the randomized Root stopping time $\tau_R=\tau_R(b,r)$ satisfies $\tau_R\le T$ and $U_{S_{\tau_R\wedge t}}=U_t$ for all $t\le T$; in particular $S_{\tau_R}\sim\mu$;
--   3. there is $\tau\in\mathcal T_T$ with $S_\tau\sim\mu$.
--
--   Furthermore, for every $\tau\in\mathcal T_T$ with $S_\tau\sim\mu$,
--   $$U_{S_{\tau\wedge t}}(x)\le U_t(x)\qquad\text{for all }x\text{ and }t\le T.$$
--
--   This is the core of the proof of Theorem 3.1: the evolutional functions are the largest potentials reachable by stopping before time $t$, and the Root time attains them.
--
--   **Formalization Note.** Equalities and inequalities between $U_{S_{\tau\wedge t}}$ and $U_t$ are stated at the integers. Both functions are linear between consecutive integers (the former because the law lives on $\mathbb Z$, the latter by the paper's interpolation), so this is equivalent to the paper's statement on $\mathbb R$. In item 2 the Root time is required to be an $(\mathcal F_t)$-stopping time and to satisfy $\tau_R\le T$ at every sample point. The law of $S_{\tau_R}$ being $\mu$ is listed as a separate conjunct, as on the page.
-- source:
--   Hu, Obłój & Zhou, When to Quit Gambling, if You Must!, arXiv:2102.03157v1, p. 46, Proposition A.3

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model

namespace CasinoCPT.Embedding

open MeasureTheory ProbabilityTheory

/-- Proposition A.3, p. 46: let `T ≥ 1` and `μ ∈ 𝒫₀(ℤ)` with `μ([-T, T]) = 1`. The following
are equivalent:
(i) `U^μ_T(x) = U_μ(x)` for all `x ∈ ℤ`;
(ii) there is a randomized Root stopping time `τ_R(b, r) ≤ T` with
`U_{S_{τ_R ∧ t}} = U^μ_t` for all `t ≤ T` (on the integers), and in particular `S_{τ_R} ∼ μ`;
(iii) there is `τ ∈ 𝒯_T` with `S_τ ∼ μ`.
Furthermore, every `τ ∈ 𝒯_T` with `S_τ ∼ μ` has `U_{S_{τ∧t}}(x) ≤ U^μ_t(x)` for all integers
`x` and `t ≤ T`. -/
theorem proposition_A_3 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (S : ℕ → Ω → ℤ) (ξ : Ω → ℝ) (hS : IsCasinoSpace P F S ξ)
    (T : ℕ) (hT : 1 ≤ T) (μ : Measure ℤ) (hμ : InP0Z μ)
    (hsupp : μ (Set.Icc (-(T : ℤ)) T) = 1) :
    List.TFAE
        [∀ x : ℤ, evol μ T x = potential μ (x : ℝ),
          ∃ (b : ℤ → ℕ) (r : ℤ → ℝ) (coin : ℕ → ℤ → Ω → Bool),
            IsRootBarrier b r ∧ IsRootCoins P F b r coin ∧
              IsStoppingTime F (rootTime S b coin) ∧ (∀ ω, rootTime S b coin ω ≤ T) ∧
              (∀ t : ℕ, t ≤ T → ∀ x : ℤ,
                potential (P.map (stoppedValue S (fun ω => min (rootTime S b coin ω) (t : ℕ∞))))
                  (x : ℝ) = evol μ t x) ∧
              P.map (stoppedValue S (rootTime S b coin)) = μ,
          ∃ τ : Ω → ℕ∞, IsAdmissible F T τ ∧ P.map (stoppedValue S τ) = μ] ∧
      ∀ τ : Ω → ℕ∞, IsAdmissible F T τ → P.map (stoppedValue S τ) = μ →
        ∀ t : ℕ, t ≤ T → ∀ x : ℤ,
          potential (P.map (stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)))) (x : ℝ) ≤
            evol μ t x := by sorry

end CasinoCPT.Embedding
