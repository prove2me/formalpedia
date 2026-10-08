-- Prove2me | Theorems.Thm_DimCallCenters_Rationalized_eq_13_14
-- name    : DimCallCenters.Rationalized.eq_13_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:57:02.340137+00:00
-- url     : https://prove2.me/theorems/16f466fc-99fe-46fe-9623-09ba3630fe15
-- title:
--   Eqs. (13)–(14) — $F_\lambda$ preserves $\stackrel{\sup}{>}$ and $\stackrel{\sup}{\gg}$
-- statement:
--   Let $\mu > 0$ and let $F$ be convex and strictly increasing on $(0,\infty)$, so that $F_\lambda$ is convex increasing with $F_\lambda(0)=0$. Let $a_\lambda, b_\lambda > 0$ for every $\lambda > 0$. Then, as $\lambda \to\infty$,
--
--   1. (13) if $\limsup a_\lambda/b_\lambda > 1$, then $\limsup F_\lambda(a_\lambda)/F_\lambda(b_\lambda) > 1$;
--   2. (14) if $\limsup a_\lambda/b_\lambda = \infty$, then $\limsup F_\lambda(a_\lambda)/F_\lambda(b_\lambda) = \infty$.
--
--   $$a_\lambda \stackrel{\sup}{>} b_\lambda \Rightarrow F_\lambda(a_\lambda) \stackrel{\sup}{>} F_\lambda(b_\lambda), \qquad a_\lambda \stackrel{\sup}{\gg} b_\lambda \Rightarrow F_\lambda(a_\lambda) \stackrel{\sup}{\gg} F_\lambda(b_\lambda).$$
--
--   Display (14) is the step in the proof of Theorem 5.1 that keeps the continuous optimum bounded.
--
--   **Formalization Note** $\limsup r_\lambda > 1$ is written as "there is $c > 1$ with $r_\lambda \ge c$ frequently", and $\limsup r_\lambda = \infty$ as "for every $C$, $r_\lambda \ge C$ frequently", avoiding `Filter.limsup` on $\mathbb R$.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 16, Section 4, Eqs. (13)-(14)

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Flam

open Filter Topology

namespace DimCallCenters.Rationalized

/-- Displays (13) and (14), p. 16. For positive functions `a_λ, b_λ`:
(13) `limsup a_λ/b_λ > 1 ⟹ limsup F_λ(a_λ)/F_λ(b_λ) > 1`;
(14) `limsup a_λ/b_λ = ∞ ⟹ limsup F_λ(a_λ)/F_λ(b_λ) = ∞`. -/
theorem eq_13_14 (μ : ℝ) (hμ : 0 < μ) (F : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (a b : ℝ → ℝ) (ha : ∀ lam : ℝ, 0 < lam → 0 < a lam) (hb : ∀ lam : ℝ, 0 < lam → 0 < b lam) :
    ((∃ c : ℝ, 1 < c ∧ ∃ᶠ lam in atTop, c ≤ a lam / b lam) →
      ∃ c : ℝ, 1 < c ∧ ∃ᶠ lam in atTop, c ≤ Flam F μ lam (a lam) / Flam F μ lam (b lam)) ∧
    ((∀ C : ℝ, ∃ᶠ lam in atTop, C ≤ a lam / b lam) →
      ∀ C : ℝ, ∃ᶠ lam in atTop, C ≤ Flam F μ lam (a lam) / Flam F μ lam (b lam)) := by sorry

end DimCallCenters.Rationalized
