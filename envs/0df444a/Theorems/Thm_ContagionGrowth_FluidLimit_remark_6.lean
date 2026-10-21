-- Prove2me | Theorems.Thm_ContagionGrowth_FluidLimit_remark_6
-- name    : ContagionGrowth.FluidLimit.remark_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:20.137494+00:00
-- url     : https://prove2.me/theorems/598e14a2-fe77-4577-adec-baca51a5d418
-- title:
--   Remark 6, p. 13 — the relaxed fixed point π* = min{π ∈ [0,1] | J^α(π) ≤ π} exists
-- statement:
--   Let $0<\alpha<1$ and let $\mu$ be a probability distribution on $\mathbb N^2$ with $\bar\lambda=\sum_{\lambda,\theta}\lambda\mu_{\lambda,\theta}\in(0,\infty)$. Let $J^\alpha(\pi)=\sum_{\lambda,\theta}\frac{\lambda\mu_{\lambda,\theta}}{\bar\lambda}B^\alpha_{\lambda,\theta}(\pi)$ and $\pi^*=\inf\{\pi\in[0,1]\mid J^\alpha(\pi)\le\pi\}$. Then
--
--   1. $J^\alpha(0)\ge0$ and $J^\alpha(1)\le1$;
--   2. the infimum is attained: $\pi^*\in[0,1]$, $J^\alpha(\pi^*)\le\pi^*$, and $\pi^*\le\pi$ for every $\pi\in[0,1]$ with $J^\alpha(\pi)\le\pi$; that is,
--   $$\pi^*=\min\{\pi\in[0,1]\mid J^\alpha(\pi)\le\pi\};$$
--   3. if $J^\alpha$ is continuous on $[0,1)$, then $J^\alpha(\pi^*)=\pi^*$.
--
--   This makes the relaxed fixed point of Theorem 5 well defined.
--
--   **Formalization Note.** $B^\alpha$ is the corrected one, $B^\alpha_{\lambda,0}:=1$ (see the definitions file). With the printed formula at $\theta=0$ the infimum need not be attained. The paper's argument mentions only item 1; attainment of the minimum is the content of "the relaxed fixed point always exists".
-- source:
--   Amini, Minca & Sulem, A dynamic contagion risk model with recovery features, preprint (February 2021), p. 13, Remark 6 (and the definition of π* in Theorem 5, p. 12)

import Mathlib
import Definitions.Def_ContagionGrowth_FluidLimit_Limit

namespace ContagionGrowth.FluidLimit

/-- Remark 6, p. 13 (existence of the relaxed fixed point): `J^α(0) ≥ 0`, `J^α(1) ≤ 1`, the
minimum defining `π*` is attained, and when `J^α` is continuous on `[0, 1)` the relaxed fixed
point is a fixed point. `B^α` is corrected at `θ = 0` (`B^α_{λ,0} := 1`). -/
theorem remark_6 (mu : ℕ × ℕ → ℝ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (hmu0 : ∀ p, 0 ≤ mu p)
    (hmu1 : HasSum mu 1) (hsum : Summable fun p : ℕ × ℕ => (p.1 : ℝ) * mu p)
    (hlb : 0 < lbar mu) :
    0 ≤ Jalpha mu α 0 ∧ Jalpha mu α 1 ≤ 1 ∧
    IsLeast {π : ℝ | π ∈ Set.Icc (0 : ℝ) 1 ∧ Jalpha mu α π ≤ π} (piStar mu α) ∧
    (ContinuousOn (Jalpha mu α) (Set.Ico 0 1) → Jalpha mu α (piStar mu α) = piStar mu α) := by sorry

end ContagionGrowth.FluidLimit
