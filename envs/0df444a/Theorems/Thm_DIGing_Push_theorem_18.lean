-- Prove2me | Theorems.Thm_DIGing_Push_theorem_18
-- name    : DIGing.Push.theorem_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:58:33.251877+00:00
-- url     : https://prove2.me/theorems/abe9762a-0b8f-443b-8f71-f0dae2e271a4
-- title:
--   Theorem 18, pp. 25–26 — Push-DIGing converges R-linearly at the explicit rate λ for every step size 0 < α < 1.5(1−δ)²/(μ̄J₂)
-- statement:
--   Let $n\ge2$ agents hold functions $f_i:\mathbb R^p\to\mathbb R$ satisfying Assumptions 4 and 5, and let $x^*$ be the minimizer of $f=\frac1n\sum_if_i$. Let the directed arc sets satisfy Assumption 6 with constant $\tilde B_\ominus$, $B_\ominus=2\tilde B_\ominus-1$, and let the mixing matrices $C(k)$ satisfy Assumption 7. Let $\|V^{-1}\|^1_{\max}=\sup_{k\ge0}\max_i1/v_i(k)$. Let $B\ge B_\ominus$ be an integer such that
--   $$\delta=Q_1\Big(1-\frac{1}{n^{(2+nB_\ominus)nB_\ominus}}\Big)^{\frac{B-1}{nB_\ominus}}<1,\qquad Q_1=2n\,\frac{1+\tilde\tau^{-nB_\ominus}}{1-\tilde\tau^{nB_\ominus}},\quad\tilde\tau=\frac{1}{n^{2+nB_\ominus}},$$
--   and define
--   $$J_2=3Q_1\|V^{-1}\|^1_{\max}\,\bar\kappa\,B\big(\delta+Q_1(B-1)\big)(1+\sqrt n)\big(1+4\sqrt n\sqrt{\bar\kappa}\big).$$
--   Then for every step size $\alpha$ with
--   $$0<\alpha<\frac{1.5(1-\delta)^2}{\bar\mu J_2},$$
--   the iterates $\mathbf x(k)$ of Push-DIGing converge to $\mathbf 1(x^*)^\top$ at a global R-linear rate $O(\lambda^k)$: $0<\lambda<1$ and there is $C>0$ with $\|\mathbf x(k)-\mathbf 1(x^*)^\top\|_F\le C\lambda^k$ for all $k$, where
--   $$\lambda=\begin{cases}\sqrt[2B]{1-\dfrac{\alpha\bar\mu}{1.5}}, & \text{if } \alpha\le\dfrac{1.5\big(\sqrt{J_2^2+(1-\delta^2)J_2}-\delta J_2\big)^2}{\bar\mu J_2(J_2+1)^2},\\[10pt] \sqrt[B]{\sqrt{\dfrac{\alpha\bar\mu J_2}{1.5}}+\delta}, & \text{otherwise.}\end{cases}$$
--
--   This is the main result for directed graphs: with a constant step size, Push-DIGing converges geometrically over time-varying directed graphs that are only jointly strongly connected, with column stochastic weights computable from out-degrees alone.
--
--   **Formalization Note** Four hypotheses are added to the page and disclosed. (1) Assumption 7 includes the self-weight $C_{jj}(k)=1/(d^{\rm out}_j(k)+1)$ of the push-sum protocol; without it $C(k)$ is not column stochastic. (2) The step-size interval is open at $1.5(1-\delta)^2/(\bar\mu J_2)$: at that endpoint the printed formula gives $\lambda=1$, which is no geometric rate. (3) $B\ge B_\ominus$, which Lemma 13 (used in the proof) requires; the page says only "large enough". (4) $n\ge2$: at $n=1$ the constant $Q_1$ has a zero denominator. $\|V^{-1}\|^1_{\max}$ is passed as a number `Vmax` with the hypothesis that it is the least upper bound of $\{1/v_i(k)\}$; the bound (49) shows this set is bounded. The constant $C$ of the rate is named `Cst` because `C` is the mixing-matrix sequence.
-- source:
--   arXiv:1607.03218v3, Theorem 18, pp. 25–26

import Mathlib
import Definitions.Def_DIGing_Undir_Common
import Definitions.Def_DIGing_Push_Setting

namespace DIGing.Push

theorem theorem_18 {n p : ℕ} (hn : 2 ≤ n) (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (Lc mu : Fin n → ℝ) (h4 : DIGing.Undir.Assumption4 f Lc) (h5 : DIGing.Undir.Assumption5 f mu)
    (xstar : EuclideanSpace ℝ (Fin p)) (hopt : ∀ z, DIGing.Undir.objective f xstar ≤ DIGing.Undir.objective f z)
    (A : ℕ → Finset (Fin n × Fin n)) (Bt : ℕ) (h6 : Assumption6 A Bt)
    (C : ℕ → Matrix (Fin n) (Fin n) ℝ) (h7 : Assumption7 A C)
    (Vmax : ℝ) (hV : IsLUB {r | ∃ k i, r = (vSeq C k i)⁻¹} Vmax)
    (B : ℕ) (hB : 2 * Bt - 1 ≤ B) (hδ : deltaPush n (2 * Bt - 1) B < 1)
    (α : ℝ) (hα : 0 < α)
    (hαmax : α < alphaMax (J2 Lc mu (2 * Bt - 1) B Vmax) (deltaPush n (2 * Bt - 1) B) (DIGing.Undir.mubar mu))
    (u x y : ℕ → DIGing.Undir.Stack n p) (hrun : IsPushDIGingRun f C α u x y) :
    0 < rateLam (J2 Lc mu (2 * Bt - 1) B Vmax) (deltaPush n (2 * Bt - 1) B) (DIGing.Undir.mubar mu) α B ∧
      rateLam (J2 Lc mu (2 * Bt - 1) B Vmax) (deltaPush n (2 * Bt - 1) B) (DIGing.Undir.mubar mu) α B < 1 ∧
      ∃ Cst : ℝ, 0 < Cst ∧ ∀ k, DIGing.Undir.frob (x k - DIGing.Undir.ones xstar) ≤
        Cst * rateLam (J2 Lc mu (2 * Bt - 1) B Vmax) (deltaPush n (2 * Bt - 1) B) (DIGing.Undir.mubar mu) α B ^ k := by sorry

end DIGing.Push
