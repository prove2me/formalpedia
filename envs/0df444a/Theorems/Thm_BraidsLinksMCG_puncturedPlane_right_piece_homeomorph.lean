-- Prove2me | Theorems.Thm_BraidsLinksMCG_puncturedPlane_right_piece_homeomorph
-- name    : BraidsLinksMCG.puncturedPlane_right_piece_homeomorph
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T07:56:02.349494+00:00
-- url     : https://prove2.me/theorems/067d089f-67f2-4a6f-8d7b-b92fc11983c6
-- title:
--   The right cover piece is homeomorphic to the complement of the origin in the plane
-- statement:
--   Let $P_{n+1} = \mathbb{E}^2 - \{1, 2, \dots, n\}$ be the plane with the $n$ points $1,\dots,n$ removed, and consider the open half-plane piece
--
--   $$R_{n+1} = \{z \in P_{n+1} \ : \ \mathrm{re}\, z > n + \tfrac34\}.$$
--
--   Geometrically $R_{n+1}$ is an open half-plane whose interior contains exactly one of the removed points, namely $n+1$. This theorem states that $R_{n+1}$ is homeomorphic to the topological space $\mathbb{C}\setminus\{0\}$, which is the standard model space for the universal covering $z \mapsto e^z$ of the punctured plane.
--
--   Explicitly, writing $w = z - (n+1)$ for the translate that moves the unique puncture to the origin, one has $\mathrm{re}\, w > -\tfrac34$ and $w \neq 0$, and the homeomorphism is
--
--   $$F(w) = \log\!\Big(1 + \tfrac43 \mathrm{re}\, w\Big) + i\,\mathrm{im}\, w,$$
--
--   with inverse
--
--   $$F^{-1}(u) = \tfrac34\big(e^{\mathrm{re}\, u} - 1\big) + i\,\mathrm{im}\, u.$$
--
--   The key point is that $u \mapsto \log(1 + \tfrac43 u)$ is a homeomorphism of the real line carrying the interval $(-\tfrac34, \infty)$ onto all of $\mathbb{R}$; the open half-plane (a strict inequality) is exactly what makes $\log$ legal, since at the boundary $u = -\tfrac34$ the argument $1 + \tfrac43 u$ vanishes. The imaginary part is carried across unchanged.
--
--   This identification is the geometric input to the computation of the fundamental group of the right cover piece: it reduces the question to the well-understood space $\mathbb{C}\setminus\{0\}$, whose fundamental group is infinite cyclic and whose universal cover is $\mathbb{C}$ via the exponential.
--
--   Formally the conclusion is `Nonempty (R_{n+1} ≃ₜ {w : ℂ // w ≠ 0})`: a `Homeomorph` is data rather than a proposition, so the existence statement is what is asserted.
-- source:
--   Classical: an open half-plane containing exactly one puncture deformation retracts onto a circle about that puncture, hence is homotopy equivalent, and here explicitly homeomorphic, to the punctured plane. The explicit homeomorphism is the standard log/exp reparameterisation of a half-plane; the universal covering of $\mathbb{C}\setminus\{0\}$ is $z\mapsto e^z$.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

open scoped Topology

/-- The right piece of the matched two-piece cover of the punctured plane is
homeomorphic to the twice-punctured-free complex plane `{w : ℂ // w ≠ 0}`, the model
space for the universal cover `exp : ℂ → {w : ℂ // w ≠ 0}`.

The map translates the unique puncture `n+1` to the origin and then straightens the
half-plane `re w > -3/4` onto the whole real line by `u ↦ log (1 + (4/3) * u)`, a
homeomorphism of the real line carrying `(-3/4, ∞)` onto `ℝ`; the imaginary coordinate
is left untouched.  It is stated as `Nonempty` because a `Homeomorph` is data, not a
proposition. -/
theorem puncturedPlane_right_piece_homeomorph (n : ℕ) :
    Nonempty
      ({z : PuncturedPlane (n + 1) | ((n : ℝ) + 1) - 3 / 4 < z.1.re} ≃ₜ
        {w : ℂ // w ≠ 0}) := by sorry

end BraidsLinksMCG
