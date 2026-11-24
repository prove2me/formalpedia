-- Prove2me | Theorems.Thm_Arxiv1510_02920_no_gain_requirements
-- name    : Arxiv1510_02920.no_gain_requirements
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:10:19.025587+00:00
-- url     : https://prove2.me/theorems/7a3be937-bfe4-4330-87db-fb9a6823ecde
-- title:
--   Eqs. (6)-(8): requirements on $f$ from the absence of gain, and the profile (8) (as proved)
-- statement:
--   Let $c>0$.
--
--   1. Let $\gamma>0$, let $f:\mathbb{R}\to\mathbb{R}$ be differentiable, and suppose the permittivity (3) with $P$ from (4) has no gain: $\operatorname{Im}\varepsilon(x,\omega)>0$ for all $x$ and all $\omega>0$. Then for every $x$
--
--   $$f'(x)\le0,\qquad c\,|f'(x)|\le4\gamma f(x),\qquad f(x)>0,$$
--
--   and $f$ is non-increasing.
--   2. Let $\Omega\ne0$, $a>0$ and $f(x)=\frac{\Omega^2}{2}[1+\tanh(-x/a)]$. Then $f'(x)<0$ for all $x$, and for all sufficiently large $\gamma$, $c\,|f'(x)|<4\gamma f(x)$ for all $x$.
--
--   **Formalization Note** Stated as proved. The paper's argument from the limits (6), (7) gives only the non-strict inequalities $f'\le0$ and $4\gamma f+cf'\ge0$; the paper's strict "$f'(x)<0$" and "$4\gamma f(x)$ must exceed $|f'(x)|$" are not necessary pointwise. The paper also omits the factor $c$, which comes from eq. (7). "As long as $\gamma$ is not too small" is read as "for all sufficiently large $\gamma$", with the threshold depending on $c$, $a$ and $\Omega$.
-- source:
--   T. G. Philbin, All-frequency reflectionlessness, arXiv:1510.02920v1 (2015), claim c005; unnumbered main text, text after eqs. (6)-(7) and eq. (8), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv1510_02920_Basic

open Filter Topology Asymptotics

namespace Arxiv1510_02920

theorem no_gain_requirements (c : ℝ) (hc : 0 < c) :
    (∀ (γ : ℝ) (f : ℝ → ℝ), 0 < γ → Differentiable ℝ f →
      (∀ x ω : ℝ, 0 < ω → 0 < (perm c (ansatzP f γ) x (ω : ℂ)).im) →
      (∀ x, deriv f x ≤ 0 ∧ c * |deriv f x| ≤ 4 * γ * f x ∧ 0 < f x) ∧ Antitone f) ∧
    (∀ Om a : ℝ, Om ≠ 0 → 0 < a →
      (∀ x, deriv (tanhProfile Om a) x < 0) ∧
      ∀ᶠ γ in atTop, ∀ x, c * |deriv (tanhProfile Om a) x| < 4 * γ * tanhProfile Om a x) := by sorry

end Arxiv1510_02920
