-- Prove2me | Theorems.Thm_CtxInvOpt_Pointed_lemma5_largest_eigenvalue
-- name    : CtxInvOpt.Pointed.lemma5_largest_eigenvalue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:14:26.272602+00:00
-- url     : https://prove2.me/theorems/363ab711-8ace-4d38-99d2-f0e6e62d3196
-- title:
--   Lemma 5, p. 20 — for d ≥ 3, λ_max(W_t) ≤ (10d/ε)^{2(d−2)} λ_max(W₁)^{d−1} e^{−I^π_t/(d−1)}; or no updates at all
-- statement:
--   Let $d=m+1\ge2$, $n\ge1$ and $\epsilon>0$. Let $C_0\subseteq S^d$ be closed and nonempty with $0<\alpha(C_0)<\pi/2$, let $c^\star\in C_0$, let $\mathcal X_t\in\mathfrak B$ and $f_t\in\mathfrak F$ for all $t$, and consider any run of EllipsoidalCones with parameter $\epsilon$, so that $W_1=\tan^2\alpha(C_0)I_{d-1}$ and $\lambda_{\min}(W_1)=\lambda_{\max}(W_1)=\tan^2\alpha(C_0)$. Write $I^\pi_t$ for the number of cone-update periods before $W_t$.
--   1. If $d\ge3$ and $\lambda_{\min}(W_1)>\big(\epsilon/(10(d-1))\big)^2$, then at every time
--   $$\lambda_{\max}(W_t)\le\Big(\frac{10d}{\epsilon}\Big)^{2(d-2)}\big(\lambda_{\max}(W_1)\big)^{d-1}e^{-I^\pi_t/(d-1)}.$$
--   2. If $\lambda_{\min}(W_1)\le\big(\epsilon/(10(d-1))\big)^2$, then there is no cone-update period at all, and the regret of every period is at most $\epsilon$.
--
--   Combined with Proposition 1, the first part bounds the number of updates after which the cone is so narrow that no further update can occur.
--
--   **Formalization Note** Part 1 is stated for $d\ge3$ only: at $d=2$ ConeUpdate halves $W$, so $\lambda_{\max}(W_t)=2^{-I^\pi_t}\lambda_{\max}(W_1)>e^{-I^\pi_t}\lambda_{\max}(W_1)$ after $I^\pi_t\ge1$ updates and the printed bound fails. Part 2 is stated for every $d\ge2$. "After $I^\pi_T$ updates, $\lambda_{\max}(W_t)\le\dots$" is stated at every time $t$ with the number of updates made so far; Lean's `w t` is the paper's $W_{t+1}$ and `updateCount … t` counts the Lean periods $s<t$. The first part is stated with the run's $\lambda_{\min}(W_1)=\tan^2\alpha(C_0)$.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 20, Lemma 5; proof App-13–App-14

import Mathlib
import Definitions.Def_CtxInvOpt_Pointed_Run

namespace CtxInvOpt.Pointed

open Matrix

/-- **Lemma 5, p. 20 (`d = m + 1 ≥ 2`; part 1 for `d ≥ 3`).** Along any run of EllipsoidalCones with parameter `ε > 0`
from a closed pointed `C₀ ⊆ S^d` (`0 < α(C₀) < π/2`), so that `W₁ = tan² α(C₀) I_{d−1}`:
1. if `d ≥ 3` and `λ_min(W₁) > (ε/(10(d−1)))²`, then at every time, after the `I^π_t` updates so far,
   `λ_max(W_t) ≤ (10d/ε)^{2(d−2)} (λ_max(W₁))^{d−1} e^{−I^π_t/(d−1)}`;
2. if `λ_min(W₁) ≤ (ε/(10(d−1)))²`, then no period is an update period and every period's regret is
   at most `ε`.
Part 1 is false at `d = 2`, where ConeUpdate halves `W` and `2^{−I} > e^{−I}`. -/
theorem lemma5_largest_eigenvalue {n m : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (C0 : Set (EuclideanSpace ℝ (Fin (m + 1)))) (hC0closed : IsClosed C0)
    (hC0 : C0 ⊆ CtxInvOpt.Offline.unitSphere (m + 1)) (hC0ne : C0.Nonempty)
    (hα0 : 0 < CtxInvOpt.Offline.uncAngle C0) (hα : CtxInvOpt.Offline.uncAngle C0 < Real.pi / 2)
    (cstar : EuclideanSpace ℝ (Fin (m + 1))) (hcstar : cstar ∈ C0)
    (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m + 1)))
    (xpi xstar : ℕ → EuclideanSpace ℝ (Fin n)) (w : ℕ → Fin m → ℝ)
    (U : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hX : ∀ t, CtxInvOpt.Offline.IsActionSet (X t)) (hf : ∀ t, CtxInvOpt.Offline.IsContext (f t))
    (hrun : IsEllConesRun ε C0 cstar X f xpi xstar w U) :
    (2 ≤ m → (ε / (10 * (m : ℝ))) ^ 2 < Real.tan (CtxInvOpt.Offline.uncAngle C0) ^ 2 →
        ∀ t, lamMax (w t) ≤
          (10 * ((m : ℝ) + 1) / ε) ^ (2 * (m - 1)) * (Real.tan (CtxInvOpt.Offline.uncAngle C0) ^ 2) ^ m *
            Real.exp (-((updateCount ε f xpi xstar w U t : ℝ) / m))) ∧
      (Real.tan (CtxInvOpt.Offline.uncAngle C0) ^ 2 ≤ (ε / (10 * (m : ℝ))) ^ 2 →
        (∀ t, updateCount ε f xpi xstar w U t = 0) ∧
          ∀ t, inner ℝ (f t (xpi t) - f t (xstar t)) cstar ≤ ε) := by sorry

end CtxInvOpt.Pointed
