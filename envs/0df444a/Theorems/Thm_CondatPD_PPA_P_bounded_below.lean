-- Prove2me | Theorems.Thm_CondatPD_PPA_P_bounded_below
-- name    : CondatPD.PPA.P_bounded_below
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:34:57.18774+00:00
-- url     : https://prove2.me/theorems/c67592f3-ce5b-4862-ad49-0c2851f001cb
-- title:
--   §4, proof of Theorem 3.2, p. 11 — if στ‖L‖² < 1, P and P′ are bounded from below
-- statement:
--   Let $\mathcal X,\mathcal Y$ be real Hilbert spaces, $L:\mathcal X\to\mathcal Y$ bounded linear, and $\tau>0$, $\sigma>0$ with
--   $$\sigma\tau\|L\|^2<1 .$$
--   Let $P$ and $P'$ be the bounded self-adjoint operators on $\mathcal Z=\mathcal X\times\mathcal Y$
--   $$P=\begin{pmatrix}\frac1\tau I&-L^*\\-L&\frac1\sigma I\end{pmatrix}\ (20),\qquad P'=\begin{pmatrix}\frac1\tau I&L^*\\L&\frac1\sigma I\end{pmatrix}\ (44).$$
--   Then $P$ and $P'$ are bounded from below on $\mathcal Z_I$: there are constants $c>0$ and $c'>0$ such that for every $z=(x,y)$
--   $$\langle z,Pz\rangle_I\ge c\,(\|x\|^2+\|y\|^2),\qquad \langle z,P'z\rangle_I\ge c'\,(\|x\|^2+\|y\|^2).$$
--
--   This is what makes $\langle z,z'\rangle_P=\langle z,Pz'\rangle_I$ a valid inner product on $\mathcal Z$ with norm equivalent to $\|\cdot\|_I$, the setting in which Algorithm 3.1 with $F=0$ is a proximal point algorithm.
--
--   **Formalization Note** "Bounded from below" is read as coercivity of the quadratic form, $\langle z,Pz\rangle_I\ge c\|z\|_I^2$ with $\|z\|_I^2=\|x\|^2+\|y\|^2$ from (19). The forms are the `qP`, `qP'` of `CondatPD.PPA.Setting`. The statement for $P'$ is the one used for Algorithm 3.2, whose analysis replaces $P$ by $P'$ (p. 13).
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 11, §4, proof of Theorem 3.2 for Algorithm 3.1, first sentence; P from (20), p. 10; P′ from (44), p. 13

import Mathlib
import Definitions.Def_CondatPD_PPA_Setting

namespace CondatPD.PPA

theorem P_bounded_below {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (L : X →L[ℝ] Y) (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (h_i : σ * τ * ‖L‖ ^ 2 < 1) :
    (∃ c : ℝ, 0 < c ∧ ∀ (x : X) (y : Y), c * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤ qP τ σ L x y) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ (x : X) (y : Y), c * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤ qP' τ σ L x y) := by sorry

end CondatPD.PPA
