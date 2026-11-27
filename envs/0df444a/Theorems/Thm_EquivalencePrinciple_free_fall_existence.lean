-- Prove2me | Theorems.Thm_EquivalencePrinciple_free_fall_existence
-- name    : EquivalencePrinciple.free_fall_existence
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T00:57:38.01781+00:00
-- url     : https://prove2.me/theorems/0efec692-e7bf-4904-b0a4-6faba2da15a7
-- title:
--   Local existence of free fall
-- statement:
--   **Local existence of free fall.**
--
--   Let `G : Vec3 → Vec3` be a gravitational field (a continuously differentiable vector field), and let a launch be given: a time `t₀`, a position `x₀` and a velocity `v₀` in space.
--
--   **Conclusion:** there exists a time window of positive length and a falling trajectory realizing the launch: some $\delta > 0$ and a twice continuously differentiable trajectory $x : \mathbb{R} \to \mathrm{Vec3}$ with
--
--   $$x(t_0) = x_0, \qquad x'(t_0) = v_0, \qquad x''(t) = G(x(t)) \ \text{ for all } t \text{ with } |t - t_0| < \delta.$$
--
--   In words: every initial condition for free fall is realized by an actual trajectory, at least for a short time — the mass ratio is normalized to $1$ ($m_g = m_i$), so this is Picard–Lindelöf for the fall equation.
--
--   **Formalization note.** Only **local**-in-time existence is asserted, deliberately: for a general $C^1$ field, solutions can blow up in finite time, so a global statement would be false. The trajectory is required to be twice continuously differentiable on all of $\mathbb{R}$ (an honest $C^2$ extension of the local solution off its window), while the law is imposed only inside the window.
-- source:
--   Wikipedia, Equivalence principle, https://en.wikipedia.org/wiki/Equivalence_principle (source of the quoted statements, reproduced verbatim in the definition file) (weak equivalence principle, realized launches); Mathlib Analysis.ODE (Picard-Lindelof existence)

import Mathlib
import Definitions.Def_EquivalencePrinciple

namespace EquivalencePrinciple

/-- Milestone: local existence of free fall.  For every gravitational field and
every launch — a time, a position and a velocity — there is a positive time
window and a twice continuously differentiable trajectory realizing the launch
and obeying the fall equation `x'' = G (x)` throughout that window (the mass
ratio is normalized to `1`, i.e. `m_g = m_i`; Picard–Lindelöf for the fall
equation).  Only local-in-time existence is asserted: for a general `C¹` field
solutions can blow up in finite time. -/
theorem free_fall_existence (G : Vec3 → Vec3) (hG : IsGravField G)
    (t₀ : ℝ) (x₀ v₀ : Vec3) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ x : ℝ → Vec3, ContDiff ℝ 2 x ∧
      x t₀ = x₀ ∧ deriv x t₀ = v₀ ∧
      (∀ t : ℝ, |t - t₀| < δ → deriv (deriv x) t = G (x t)) := by
  sorry

end EquivalencePrinciple
