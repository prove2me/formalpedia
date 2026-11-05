-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasLoopWind_ccwLoop_annulus_eq_add_sum
-- name    : FiniteEnergyPlane.hasLoopWind_ccwLoop_annulus_eq_add_sum
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T20:11:18.893238+00:00
-- url     : https://prove2.me/theorems/ece2157f-1ee4-4e47-958b-b781ddb1c6ac
-- title:
--   Argument principle for continuous functions on a closed annulus
-- statement:
--   Let $0<a<b$, let $P\subset\{a<|z|<b\}$ be finite, and let $g$ be continuous and nowhere zero on $\{a\le|z|\le b\}\setminus P$. Suppose $g$ has winding number $m_0$ along the counterclockwise circle $|z|=a$, and that for each $p\in P$ it has winding number $m_p$ along every counterclockwise circle of sufficiently small radius about $p$. Then $g$ has winding number
--   $$m_0+\sum_{p\in P}m_p$$
--   along the counterclockwise circle $|z|=b$.
--
--   This is the argument principle for continuous functions on a closed annulus. It assumes nothing about $g$ on the disc $\{|z|<a\}$.
--
--   **Formalization Note** Circles are `ccwLoop ρ t` $=\rho e^{2\pi it}$, and winding numbers are `HasLoopWind`.
-- source:
--   U. Hryniewicz, Trans. AMS 364 (2012), arXiv:1105.2077, Section 4.6; H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- Argument principle on an annulus. Let `0 < a < b`, let `P ⊂ {a < ‖z‖ < b}` be finite and `g`
continuous and nowhere zero on `{a ≤ ‖z‖ ≤ b} \ P`. If `g` has winding number `m₀` along the
counterclockwise circle of radius `a`, and for each `p ∈ P` winding number `m p` along every
counterclockwise circle of small radius about `p`, then it has winding number
`m₀ + ∑_{p ∈ P} m p` along the counterclockwise circle of radius `b`. -/
theorem hasLoopWind_ccwLoop_annulus_eq_add_sum (g : ℂ → ℂ) (P : Finset ℂ) (a b : ℝ) (ha : 0 < a)
    (hab : a < b) (hP : ∀ p ∈ P, a < ‖p‖ ∧ ‖p‖ < b)
    (hg : ContinuousOn g ({z | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} \ ↑P))
    (hg0 : ∀ z ∈ {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} \ ↑P, g z ≠ 0) (m₀ : ℤ)
    (hm₀ : HasLoopWind (fun t => g (ccwLoop a t)) m₀) (m : ℂ → ℤ)
    (hm : ∀ p ∈ P, ∃ r > (0 : ℝ), ∀ ρ ∈ Set.Ioo 0 r,
      HasLoopWind (fun t => g (p + ccwLoop ρ t)) (m p)) :
    HasLoopWind (fun t => g (ccwLoop b t)) (m₀ + ∑ p ∈ P, m p) := by
  sorry

end FiniteEnergyPlane
