-- Prove2me | Theorems.Thm_FiniteEnergyPlane_fderiv_endA_eq_liouville_endW
-- name    : FiniteEnergyPlane.fderiv_endA_eq_liouville_endW
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-29T22:04:13.069232+00:00
-- url     : https://prove2.me/theorems/0d96d1a2-3959-4aed-bef3-f0f17aafc56f
-- title:
--   Cauchy–Riemann equations of a J̃-holomorphic curve in the symplectization coordinates along a cylindrical end
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^{2n+2}$ be a strictly star-shaped level, $\lambda_0 = \tfrac12 \sum_k (q_k\,dp_k - p_k\,dq_k)$ the Liouville form, and $J$ a compatible complex structure on the contact planes $\xi$. Let $\tilde J$ be the induced almost complex structure on $\mathbb{R}^{2n+2} \setminus \{0\} \cong \mathbb{R} \times S$, with coordinates $y = e^{2a} w$, $w \in S$.
--
--   Let $u : \mathbb{D} \setminus \{0\} \to \mathbb{R}^{2n+2} \setminus \{0\}$ be $\tilde J$-holomorphic, and write $a(s,t)$, $w(s,t)$ for its coordinates in the positive cylindrical coordinates $(s, t) \mapsto e^{-2\pi(s + it)}$ at the puncture $0$.
--
--   Then for every $s > 0$ and $t \in \mathbb{R}$, $a$ and $w$ are differentiable at $(s,t)$ and
--   $$\partial_s a = \lambda_0(w)(\partial_t w), \qquad \partial_t a = -\lambda_0(w)(\partial_s w).$$
--
--   This expresses the $\mathbb{R}$-component of the Cauchy–Riemann equation $\partial_s u + \tilde J(u)\,\partial_t u = 0$ in the coordinates on an end, the form used to compare $a$ with the period coordinate of a nearby Reeb orbit.
--
--   **Formalization Note.** $u$ is assumed $\tilde J$-holomorphic and nonvanishing on `ball 0 1 \ {0}`; the end coordinates are `endA H u cylEnd` and `endW H u cylEnd`, partial derivatives are `fderiv` applied to `(1, 0)` and `(0, 1)`, and $\lambda_0(w)(v)$ is `liouville w v`.
-- source:
--   Used for U. Hryniewicz, J. Symplectic Geom. 12 (2014), Theorem 2.10; see also H. Hofer, Invent. Math. 114 (1993), § 3, and C. Wendl, Lectures on Symplectic Field Theory, Lecture 9

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

/-- The Cauchy–Riemann equations of a `J̃`-holomorphic curve in the coordinates `(a, w)` along
the cylindrical end at the puncture `0`. Let `u` be `J̃`-holomorphic on `D \ {0}` and nonvanishing
there. For `s > 0`, the coordinates `a = endA` and `w = endW` in the cylindrical coordinates
`cylEnd` are differentiable at `(s, t)` and satisfy `∂ₛa = λ_w(∂ₜw)` and `∂ₜa = -λ_w(∂ₛw)`,
where `λ_w(v) = ½ ω₀(w, v)` is the Liouville form. -/
theorem fderiv_endA_eq_liouville_endW {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : JHolomorphic.IsJHolomorphicOn (Jtilde H J) (ball 0 1 \ {0}) u)
    (hu0 : ∀ z ∈ ball (0 : ℂ) 1 \ {0}, u z ≠ 0) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    DifferentiableAt ℝ (endA H u cylEnd) (s, t) ∧ DifferentiableAt ℝ (endW H u cylEnd) (s, t) ∧
      fderiv ℝ (endA H u cylEnd) (s, t) (1, 0) =
        liouville (endW H u cylEnd (s, t)) (fderiv ℝ (endW H u cylEnd) (s, t) (0, 1)) ∧
      fderiv ℝ (endA H u cylEnd) (s, t) (0, 1) =
        -liouville (endW H u cylEnd (s, t)) (fderiv ℝ (endW H u cylEnd) (s, t) (1, 0)) := by
  sorry

end FiniteEnergyPlane
