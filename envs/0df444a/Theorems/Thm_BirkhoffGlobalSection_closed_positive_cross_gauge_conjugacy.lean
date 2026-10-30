-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_closed_positive_cross_gauge_conjugacy
-- name    : BirkhoffGlobalSection.closed_positive_cross_gauge_conjugacy
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T19:30:28.403857+00:00
-- url     : https://prove2.me/theorems/0e2951f7-6e7c-40e5-933f-9834082ecb90
-- title:
--   Closed positive-cross-product changes of coordinates conjugate endpoint angles
-- statement:
--   Let $A_t$ be a continuous family of real-linear maps of the complex plane for $0\le t\le1$, with $A_1=A_0$ and $\operatorname{Im}(\overline z A_tz)>0$ for every nonzero $z$. Let $w_t$ be a continuous nonzero complex path, and let $\theta_t$ be a continuous polar angle of $A_tw_t$ with positive amplitude. Then $w_t$ has a continuous angle lift $\beta_t$ starting at some $s\in[0,2\pi)$, and there is a strictly increasing map $a:\mathbb R\to\mathbb R$ satisfying
--
--   $$a(u+2\pi)=a(u)+2\pi,\qquad \theta_1-\theta_0=a(\beta_1)-a(s).$$
--
--   The conclusion also supplies positive amplitudes for $w_t$. This gives an endpoint winding comparison for a closed moving change of transverse frame.
-- source:
--   Derived supporting lemma for BirkhoffGlobalSection.radial_contact_transverse_angle_conjugacy, https://prove2.me/theorems/eab3aa7c-2cfb-4515-b659-4ccc36142c64. The continuous-path lifting step specializes Mathlib Analysis/Complex/CoveringMap.lean (isCoveringMap_exp); the local C2 Hamiltonian identities adapt Mazecto accepted submission 893234ef-5ec2-4f4b-b415-f79ec1030002 without strengthening regularity.

import Mathlib

theorem BirkhoffGlobalSection.closed_positive_cross_gauge_conjugacy (A : ℝ → (ℂ →L[ℝ] ℂ))
    (hAc : ContinuousOn A (Set.Icc 0 1)) (hAend : A 1 = A 0)
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, z ≠ 0 → 0 < (star z * A t z).im)
    (w : ℝ → ℂ) (hw : ContinuousOn w (Set.Icc 0 1))
    (hwne : ∀ t ∈ Set.Icc (0 : ℝ) 1, w t ≠ 0)
    (θ : ℝ → ℝ) (hθc : ContinuousOn θ (Set.Icc 0 1))
    (hθ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ ρ : ℝ, 0 < ρ ∧ A t (w t) = (ρ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)) :
    ∃ (s : ℝ) (β a : ℝ → ℝ),
      s ∈ Set.Ico (0 : ℝ) (2 * Real.pi) ∧ Continuous β ∧ β 0 = s ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧ w t = (r : ℂ) * Complex.exp ((β t : ℂ) * Complex.I)) ∧
      StrictMono a ∧ (∀ u : ℝ, a (u + 2 * Real.pi) = a u + 2 * Real.pi) ∧
      θ 1 - θ 0 = a (β 1) - a s := by sorry
