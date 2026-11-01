-- Prove2me | Theorems.Thm_DoublyOptBandit_lemma_2_12
-- name    : DoublyOptBandit.lemma_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:47.242365+00:00
-- url     : https://prove2.me/theorems/8d5299c2-e0d7-443f-9537-a5cc9988568b
-- title:
--   Lemma 2.12 — one-step descent inequality for Algorithm 1
-- statement:
--   Let $X\subseteq\mathbb R^n$ ($n\ge1$) be closed, convex and compact with nonempty interior, $R$ a $\nu$-self-concordant barrier for $X$ and $\beta>0$. Let the iterates $x_t$ of Algorithm 1 be generated from reward functions $u_t$ with $|u_t(x)|\le L$ for all $x\in X$ and a non-increasing step size with $0<\eta_t\le\frac1{2nL}$. Then for every realization of the directions $z_t$ on the unit sphere, every round $t\ge1$ and every $p\in X$,
--   $$
--   D_R(p,x_{t+1})+\frac{\eta_t\beta(t+1)}2\|x_{t+1}-p\|^2\le D_R(p,x_t)+\frac{\eta_t\beta(t+1)}2\|x_t-p\|^2+2\eta_t^2\|A_t\hat v_t\|^2+\eta_t\langle\hat v_t,x_t-p\rangle ,
--   $$
--   where $A_t$ is the scaling matrix, $\hat v_t$ the gradient estimate of round $t$, and $D_R$ the Bregman divergence (2.3).
--
--   Summed over rounds, this inequality drives the regret bound of Algorithm 1, and applied to each player it gives Lemma 3.10.
--
--   Differences from the source:
--   - generalization: rewards u₁, …, u_T smooth and β-strongly concave (standing assumption of §2.4) → arbitrary functions uₜ with |uₜ(x)| ≤ L on X; reason: the inequality uses only |uₜ(x̂ₜ)| ≤ L (proof, Appendix A, p.27); the source's rewards are instances
--   - encoding: random directions zₜ ∼ Sⁿ → every sequence of directions with ‖zₜ‖ = 1 (pathwise); reason: the lemma is an inequality for each realization of the draws
--   - encoding: dimension n and set X with interior → n ≥ 1 and int X nonempty; reason: Sⁿ is empty for n = 0, and R : int(X) → ℝ and x₁ = argmin R need int X ≠ ∅
--   - encoding: 0 < ηₜ ≤ 1/(2nL) → the same with Lean's 1/0 = 0, so L = 0 makes the hypothesis unsatisfiable; reason: 1/(2nL) is undefined at L = 0; only that undefined case is excluded
--   - encoding: argmin over X in (2.5) and in the initialization → argmin over int X; reason: the objectives contain R, defined on int X only
-- source:
--   Ba, Lin, Zhang & Zhou, Doubly Optimal No-Regret Online Learning in Strongly Monotone Games with Bandit Feedback, arXiv:2112.02856v4, Lemma 2.12, p.9; Algorithm 1, p.9; (2.5), p.8; standing assumptions of §2.4, p.8

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier
import Definitions.Def_DoublyOptBandit_Algorithm1

open scoped InnerProductSpace

namespace DoublyOptBandit

/-- **Lemma 2.12** (descent inequality for Algorithm 1; Ba, Lin, Zhang & Zhou,
arXiv:2112.02856v4, Lemma 2.12, p.9). Let `X ⊆ ℝⁿ` be closed, convex and compact with nonempty
interior, `R` a `ν`-self-concordant barrier for `X`, `β > 0`, and let the iterates `xₜ` be generated
by Algorithm 1 from rewards `uₜ` with `|uₜ(x)| ≤ L` on `X` and a non-increasing step size with
`0 < ηₜ ≤ 1/(2nL)`. Then for every realization of the directions `zₜ` on the unit sphere, every round
`t ≥ 1` and every `p ∈ X`,
`D_R(p, xₜ₊₁) + (ηₜβ(t+1)/2)‖xₜ₊₁ − p‖² ≤ D_R(p, xₜ) + (ηₜβ(t+1)/2)‖xₜ − p‖² + 2ηₜ²‖Aₜv̂ₜ‖² +
ηₜ⟨v̂ₜ, xₜ − p⟩`.

**Formalization Note** The inequality is pathwise: it holds for every sequence of directions with
`‖zₜ‖ = 1`. The rewards `uₜ` are arbitrary functions bounded by `L` on `X`; the smoothness and
strong concavity of §2.4's adversary are not assumed. `D_R(p, x)` is
`BeckTeboulleMD.EMDA.bregman R p x`; since `R(p)` cancels from the two sides, the statement is
meaningful for every `p ∈ X`. The dimension `n` is `m ≥ 1` (the unit sphere of `ℝ⁰` is empty). -/
theorem lemma_2_12 {m : ℕ} (hm : 1 ≤ m) (X : Set (EuclideanSpace ℝ (Fin m)))
    (hXc : IsCompact X) (hXcv : Convex ℝ X) (hXi : (interior X).Nonempty)
    (R : EuclideanSpace ℝ (Fin m) → ℝ) (ν : ℝ)
    (hR : EntropicBarrier.Universal.IsNuSelfConcordantBarrier X R ν)
    (β : ℝ) (hβ : 0 < β) (L : ℝ) (u : ℕ → EuclideanSpace ℝ (Fin m) → ℝ)
    (hu : ∀ t, ∀ x ∈ X, |u t x| ≤ L) (η : ℕ → ℝ)
    (hη : ∀ t, 1 ≤ t → 0 < η t ∧ η t ≤ 1 / (2 * (m : ℝ) * L))
    (hηmono : ∀ t, 1 ≤ t → η (t + 1) ≤ η t)
    (z : ℕ → EuclideanSpace ℝ (Fin m)) (hz : ∀ t, ‖z t‖ = 1)
    (t : ℕ) (ht : 1 ≤ t) (p : EuclideanSpace ℝ (Fin m)) (hp : p ∈ X) :
    BeckTeboulleMD.EMDA.bregman R p (alg1Iter X R β η u z (t + 1)) +
        η t * β * ((t : ℝ) + 1) / 2 * ‖alg1Iter X R β η u z (t + 1) - p‖ ^ 2 ≤
      BeckTeboulleMD.EMDA.bregman R p (alg1Iter X R β η u z t) +
        η t * β * ((t : ℝ) + 1) / 2 * ‖alg1Iter X R β η u z t - p‖ ^ 2 +
        2 * η t ^ 2 *
          ‖Matrix.toEuclideanLin (alg1Scaling X R β η u z t) (alg1Estimate X R β η u z t)‖ ^ 2 +
        η t * ⟪alg1Estimate X R β η u z t, alg1Iter X R β η u z t - p⟫_ℝ := by sorry

end DoublyOptBandit
