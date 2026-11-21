-- Prove2me | Theorems.Thm_FiniteEnergyPlane_bounded_iteratedFDeriv_of_comp_immersion
-- name    : FiniteEnergyPlane.bounded_iteratedFDeriv_of_comp_immersion
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T17:43:02.41176+00:00
-- url     : https://prove2.me/theorems/6bd1f73d-68c8-484f-a6e4-d63b7443db4f
-- title:
--   Derivative bounds through a uniform immersion on a cylindrical end
-- statement:
--   Let $E, F$ be real normed spaces, $\Omega \subseteq E$ open and $\Xi : E \to F$ smooth on $\Omega$. Let $X : \mathbb{R} \times \mathbb{R} \to E$ be smooth on the end $(s_0, \infty) \times \mathbb{R}$ with $X(s, t) \in \Omega$ for $s > s_0$. Suppose that:
--   - for every $m \ge 1$, $\|D^m \Xi(X(s, t))\|$ is bounded for $s \ge s_1(m)$, uniformly in $t$;
--   - for some $c > 0$, $c\,\|h\| \le \|D\Xi(X(s, t)) h\|$ for all $s > s_0$, all $t$ and all $h \in E$;
--   - for every $m \ge 1$, $\|D^m(\Xi \circ X)(s, t)\|$ is bounded for $s \ge s_1(m)$, uniformly in $t$.
--
--   Then for every $m \ge 1$ there are $C, s_1$ with $\|D^m X(s, t)\| \le C$ for all $s \ge s_1$ and all $t$.
--
--   Role: transfers uniform derivative bounds through a map that is a uniform immersion along $X$; used to obtain uniform $C^\infty$ bounds of coordinates on a cylindrical end from those of their image.
--
--   Formalization note: derivatives are `iteratedFDeriv ℝ m`; the end is `Set.Ioi s₀ ×ˢ Set.univ`.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6

import Mathlib

namespace FiniteEnergyPlane

open Set
open scoped ContDiff

/-- Derivative bounds through a uniform immersion. Let `Ξ` be smooth on an open set `Ω` and let
`X` be smooth on the end `(s₀, ∞) × ℝ` with values in `Ω`. Suppose that along `X` every
derivative `D^m Ξ` with `m ≥ 1` is bounded far out on the end and `c ‖h‖ ≤ ‖DΞ(X(s, t)) h‖`. If
every derivative of order `≥ 1` of `Ξ ∘ X` is bounded far out on the end, then so is every
derivative of order `≥ 1` of `X`. -/
theorem bounded_iteratedFDeriv_of_comp_immersion {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ξ : E → F) (Ω : Set E) (hΩ : IsOpen Ω) (hΞ : ContDiffOn ℝ ∞ Ξ Ω)
    (X : ℝ × ℝ → E) (s₀ : ℝ) (hX : ContDiffOn ℝ ∞ X (Ioi s₀ ×ˢ univ))
    (hXΩ : ∀ s > s₀, ∀ t : ℝ, X (s, t) ∈ Ω)
    (hΞb : ∀ m : ℕ, 1 ≤ m → ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m Ξ (X (s, t))‖ ≤ C)
    (c : ℝ) (hc : 0 < c)
    (hlow : ∀ s > s₀, ∀ t : ℝ, ∀ h : E, c * ‖h‖ ≤ ‖fderiv ℝ Ξ (X (s, t)) h‖)
    (hY : ∀ m : ℕ, 1 ≤ m → ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p => Ξ (X p)) (s, t)‖ ≤ C) :
    ∀ m : ℕ, 1 ≤ m → ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖iteratedFDeriv ℝ m X (s, t)‖ ≤ C := by
  sorry

end FiniteEnergyPlane
