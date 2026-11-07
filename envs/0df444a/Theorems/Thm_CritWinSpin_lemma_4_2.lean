-- Prove2me | Theorems.Thm_CritWinSpin_lemma_4_2
-- name    : CritWinSpin.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:40:07.304286+00:00
-- url     : https://prove2.me/theorems/1ab44614-d046-484c-9258-1d5fdd37afea
-- title:
--   Lemma 4.2, p.14 — $g_s$ is a $C^1$ convex envelope and $0\le d_s\le\Delta_s=O((s-\tau)^{p/(p-1)})$
-- statement:
--   Let $\rho$ be GHS of type $p$ and $s>\tau$. The equation $a=s\phi'(a)$ has a unique positive solution $a_s$, and:
--
--   1. $g_s$ is convex and continuously differentiable on $\mathbb R$, and for $|t|\ne a_s$,
--   $$|\phi_s'(t)|\le1,\qquad|d_s'(t)|\le1,\qquad0\le\phi_s''(t)\le\frac1s;$$
--   2. for all $t$,
--   $$0\le d_s(t)\le\Delta_s:=\sup_{|m|\le1}\Bigl\{\frac s2m^2-I(m)\Bigr\}\le C(s-\tau)^{p/(p-1)},$$
--   with $C$ depending only on $\rho$ and $p$.
--
--   This bounds the potential gap that the sampler pays for exponentially.
--
--   Differences from the source:
--   - reading: Δ_s = O((s − τ)^{p/(p−1)}) → Δ_s ≤ C (s − τ)^{p/(p−1)} for every s > τ, with C before s; reason: the strong reading; the proof on p.15 gives this for every s > τ
--   - encoding: a_s > 0 is the unique positive solution (stated before the lemma) → existence and uniqueness are conclusions, and a_s is the supremum of the solution set; reason: so that no hypothesis assumes them
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Lemma 4.2, p.14, eqs. (21), (22); the definition of a_s, p.14

import Mathlib
import Definitions.Def_CritWinSpin_Wpot
set_option autoImplicit false

namespace CritWinSpin

/-- **Lemma 4.2** (Liu–Zhang–Ren, STOC 2027 submission, manuscript sha256 f77584da…, p.14). For `s > τ`:
`a_s` is the unique positive solution of `a = s ϕ'(a)`; (i) `g_s` is convex and `C¹`, and off `|t| = a_s`,
`|ϕ_s'| ≤ 1`, `|d_s'| ≤ 1`, `0 ≤ ϕ_s'' ≤ 1/s`, eq. (21); (ii) `0 ≤ d_s ≤ Δ_s = O((s − τ)^{p/(p−1)})`, eq. (22). -/
theorem lemma_4_2 (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, tau S < s →
      (∃! a : ℝ, 0 < a ∧ a = s * deriv (phi S) a) ∧
      (0 < asOf S s ∧ asOf S s = s * deriv (phi S) (asOf S s)) ∧
      ConvexOn ℝ Set.univ (gs S s) ∧ ContDiff ℝ 1 (gs S s) ∧
      (∀ t : ℝ, |t| ≠ asOf S s →
        |deriv (phis S s) t| ≤ 1 ∧ |deriv (ds S s) t| ≤ 1 ∧
        0 ≤ iteratedDeriv 2 (phis S s) t ∧ iteratedDeriv 2 (phis S s) t ≤ 1 / s) ∧
      (∀ t : ℝ, 0 ≤ ds S s t ∧ ds S s t ≤ deltaS S s) ∧
      deltaS S s ≤ C * (s - tau S) ^ ((p : ℝ) / ((p : ℝ) - 1)) := by sorry

end CritWinSpin
