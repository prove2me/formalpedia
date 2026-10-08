-- Prove2me | Theorems.Thm_EkelandVP_General_ekeland_variational_principle
-- name    : EkelandVP.General.ekeland_variational_principle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T10:26:08.559063+00:00
-- url     : https://prove2.me/theorems/75865e65-db9d-48e0-8401-385743f99e68
-- title:
--   Theorem 1.1, p. 324 — Ekeland's variational principle
-- statement:
--   Let $(V,d)$ be a complete metric space and $F : V\to\mathbb{R}\cup\{+\infty\}$ a lower semicontinuous function which is not identically $+\infty$ and is bounded from below, $\inf F > -\infty$ (1.1). Let $\varepsilon>0$ and let $u\in V$ satisfy
--
--   $$
--   \inf F \le F(u) \le \inf F + \varepsilon. \tag{1.2}
--   $$
--
--   Then for every $\lambda > 0$ there is a point $v\in V$ such that
--
--   $$
--   F(v)\le F(u), \qquad d(u,v)\le\lambda, \qquad F(w) > F(v) - \frac{\varepsilon}{\lambda}\, d(v,w)\quad\text{for all } w\ne v. \tag{1.3–1.5}
--   $$
--
--   In words: near any $\varepsilon$-minimizer $u$ lies a point $v$ which is no worse, within distance $\lambda$ of $u$, and is the unique (strict) minimizer of the perturbed function $w\mapsto F(w)+\frac{\varepsilon}{\lambda}d(v,w)$. No compactness is required; the infimum of $F$ need not be attained. The rest of the paper applies this result to Gâteaux-differentiable functions, constrained optimization, geodesics and optimal control.
--
--   **Formalization Note** $F$ takes values in `EReal`; the hypothesis $\bot < \inf F$ expresses (1.1) and also excludes the value $-\infty$, which the paper's codomain $\mathbb{R}\cup\{+\infty\}$ does not contain. "Not identically $+\infty$" is the existence of $v_0$ with $F(v_0)\ne+\infty$. Only the right half of (1.2) is assumed, since $\inf F\le F(u)$ always holds. $\lambda$ is a Lean keyword and is named `lam`. Conclusion (1.5) is written $F(v) - \frac{\varepsilon}{\lambda}d(v,w) < F(w)$; under the hypotheses $F(v)$ is finite, so this `EReal` subtraction is ordinary real subtraction.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 324, Theorem 1.1, (1.1)–(1.5)

import Mathlib

namespace EkelandVP.General

theorem ekeland_variational_principle {V : Type*} [MetricSpace V] [CompleteSpace V]
    (F : V → EReal) (hF : LowerSemicontinuous F) (hne : ∃ v₀ : V, F v₀ ≠ ⊤)
    (hbdd : ⊥ < ⨅ v, F v) (ε : ℝ) (hε : 0 < ε) (u : V)
    (hu : F u ≤ (⨅ v, F v) + (ε : EReal)) (lam : ℝ) (hlam : 0 < lam) :
    ∃ v : V, F v ≤ F u ∧ dist u v ≤ lam ∧
      ∀ w : V, w ≠ v → F v - ((ε / lam * dist v w : ℝ) : EReal) < F w := by sorry

end EkelandVP.General
