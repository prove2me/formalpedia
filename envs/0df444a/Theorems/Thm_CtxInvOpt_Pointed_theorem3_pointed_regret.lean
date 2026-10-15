-- Prove2me | Theorems.Thm_CtxInvOpt_Pointed_theorem3_pointed_regret
-- name    : CtxInvOpt.Pointed.theorem3_pointed_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:14:28.461714+00:00
-- url     : https://prove2.me/theorems/a4bde05a-249f-4672-be27-908b339eeb72
-- title:
--   Theorem 3, p. 20 — with ε = d/T, EllipsoidalCones has regret O(d² ln(T tan α(C₀))), or O(d) when α(C₀) ≤ arctan(d/T)
-- statement:
--   Run EllipsoidalCones with $\epsilon=d/T$. There is an absolute constant $K$ such that the following holds for every cost dimension $d=m+1\ge2$, action dimension $n\ge1$ and horizon $T\ge1$. Let $C_0\subseteq S^d$ be closed and nonempty with $0<\alpha(C_0)<\pi/2$, let $c^\star\in C_0$, let $\mathcal X_t\in\mathfrak B$ and $f_t\in\mathfrak F$ for every $t$ (chosen by nature, possibly adaptively), and consider any run of the algorithm. Then:
--   1. if $\alpha(C_0)>\arctan(d/T)$,
--   $$\mathcal R^\pi_T\big(c^\star,\vec{\mathcal X}_T,\vec f_T\big)\le K\,d^2\ln\big(T\tan\alpha(C_0)\big);$$
--   2. if $\alpha(C_0)\le\arctan(d/T)$,
--   $$\mathcal R^\pi_T\big(c^\star,\vec{\mathcal X}_T,\vec f_T\big)\le K\,d.$$
--
--   Since the bound holds for every $c^\star\in C_0$ and every admissible instance sequence, it bounds the worst-case regret $\mathcal{WCR}^\pi_T(C_0)$. This is the paper's logarithmic-regret guarantee for a pointed initial knowledge set, in contrast with the linear regret the greedy circumcenter policy can incur.
--
--   **Formalization Note** $\mathcal O(\cdot)$ is read as an absolute constant $K$ chosen before $d$, $n$, $T$, $C_0$ and the run. In case 1, $T\tan\alpha(C_0)>d\ge2$, so the logarithm is positive. The hypothesis $\alpha(C_0)>0$ excludes the degenerate case where $C_0$ is a single point and the algorithm's $W_1=0$ is not positive definite (the regret is then $0$). The sentence "This algorithm runs in polynomial time in $d$ and $T$" is not formalized. The worst-case regret is stated as a bound for every $c^\star$, instance and run rather than as a real supremum. Lean periods are $0$-based and the regret sums the Lean periods $t<T$.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 20, Theorem 3; proof App-14–App-16

import Mathlib
import Definitions.Def_CtxInvOpt_Pointed_Run

namespace CtxInvOpt.Pointed

open Matrix

/-- **Theorem 3, p. 20.** There is an absolute constant `K` such that, for every dimension `d = m + 1 ≥ 2`,
action dimension `n ≥ 1`, horizon `T ≥ 1`, closed pointed initial knowledge set `C₀ ⊆ S^d` with
`0 < α(C₀) < π/2`, true cost `c⋆ ∈ C₀`, admissible instance sequence and every run of EllipsoidalCones
with `ε = d/T`: if `α(C₀) > arctan(d/T)` the regret over `T` periods is at most
`K d² ln(T tan α(C₀))`, and if `α(C₀) ≤ arctan(d/T)` it is at most `K d`. -/
theorem theorem3_pointed_regret :
    ∃ K : ℝ, ∀ (m n T : ℕ), 1 ≤ m → 1 ≤ n → 1 ≤ T →
      ∀ C0 : Set (EuclideanSpace ℝ (Fin (m + 1))), IsClosed C0 → C0 ⊆ CtxInvOpt.Offline.unitSphere (m + 1) →
        C0.Nonempty → 0 < CtxInvOpt.Offline.uncAngle C0 → CtxInvOpt.Offline.uncAngle C0 < Real.pi / 2 →
        ∀ cstar ∈ C0,
        ∀ (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
          (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m + 1)))
          (xpi xstar : ℕ → EuclideanSpace ℝ (Fin n)) (w : ℕ → Fin m → ℝ)
          (U : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ),
        (∀ t, CtxInvOpt.Offline.IsActionSet (X t)) → (∀ t, CtxInvOpt.Offline.IsContext (f t)) →
        IsEllConesRun (((m : ℝ) + 1) / T) C0 cstar X f xpi xstar w U →
        (Real.arctan (((m : ℝ) + 1) / T) < CtxInvOpt.Offline.uncAngle C0 →
            CtxInvOpt.Greedy.cumRegret cstar f xpi xstar T ≤
              K * ((m : ℝ) + 1) ^ 2 * Real.log (T * Real.tan (CtxInvOpt.Offline.uncAngle C0))) ∧
          (CtxInvOpt.Offline.uncAngle C0 ≤ Real.arctan (((m : ℝ) + 1) / T) →
            CtxInvOpt.Greedy.cumRegret cstar f xpi xstar T ≤ K * ((m : ℝ) + 1)) := by sorry

end CtxInvOpt.Pointed
