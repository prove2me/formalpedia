-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_stdTube_of_isFastPlane
-- name    : FiniteEnergyPlane.exists_stdTube_of_isFastPlane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T13:00:31.937426+00:00
-- url     : https://prove2.me/theorems/629359c7-121d-4f5f-9b28-fad8fb00030c
-- title:
--   A standard tube around a fast finite-energy plane
-- statement:
--   Let $H$ be a strictly star-shaped level function on $\mathbb{R}^4$, $J$ a compatible complex structure on the contact structure $\xi$, $\tilde J$ the induced almost complex structure on the symplectization $\mathbb{R}^4 \setminus \{0\}$ (`Jtilde H J`), and $P = (x, T)$ a periodic Reeb orbit. Let $u : \mathbb{C} \to \mathbb{R}^4 \setminus \{0\}$ be a fast finite-energy plane (`IsFastPlane H J u`) with a nondegenerate end at $P$ (`IsNondegenerateEnd H u cylInf P 1`).
--
--   Then there are $\rho, b > 0$, a $C^\infty$ map $\Phi : \mathbb{C} \times \mathbb{C} \to \mathbb{R}^4$ and a standard tube structure $(\bar J, J_\infty, S_\infty)$ of width $\rho$ and rate $b$ (`IsStdTubeStructure ρ b Jbar Jinf Sinf`) such that:
--
--   1. $\Phi(z, 0) = u(z)$ for all $z$.
--   2. For every $p \in \mathbb{C} \times B_\rho(0)$: $\Phi(p) \neq 0$, $D\Phi(p)$ is injective, and $D\Phi(p) \circ \bar J(p) = \tilde J(\Phi(p)) \circ D\Phi(p)$.
--   3. There is $\tau \in \mathbb{C}$ with $D\Phi(0, 0)(\tau, 1) = u(0)$.
--   4. There are $d, c \in \mathbb{R}$ and functions $\alpha : \mathbb{R} \times \mathbb{C} \to \mathbb{R}$, $X : \mathbb{R} \times \mathbb{C} \to \mathbb{R}^4$, smooth on $\mathbb{R} \times B_\rho(0)$ and $1$-periodic in $t$, with $\alpha(t, 0) = 0$ and $X(t, 0) = x(Tt + c)$, such that, writing $\Phi$ in the coordinates $(s, t, w) \mapsto \Phi(e^{2\pi(s + it)}, w)$ and in the splitting $(a, \mathrm{proj})$ of the symplectization (`aCoord`, `proj`), the functions
--   $$a\big(\Phi(e^{2\pi(s+it)}, w)\big) - Ts - d - \alpha(t, w), \qquad \mathrm{proj}\big(\Phi(e^{2\pi(s+it)}, w)\big) - X(t, w)$$
--   decay exponentially at rate $b$ in $C^\infty$ as $s \to \infty$, uniformly in $t$ and $w \in B_\rho(0)$ (`ExpDecayCInftyTube`).
--   5. If $\mu$ is an eigenvalue of $-J_0 \partial_t - S_\infty$ on loops (`IsLoopEigen Sinf μ e`), then $\mu$ is an eigenvalue of the asymptotic operator $A_P$ (`IsAsymptoticEigen J P μ v` for some $v$).
--   6. If $\mu$ is an eigenvalue of $-J_0\partial_t - S_\infty$ with an eigenfunction of winding number $k$ (`HasLoopEigenWind Sinf μ k`), then $\mu$ is an eigenvalue of $A_P$ of winding number $k + 1$ (`HasEigenWind J P μ (k + 1)`).
--
--   **Role.** Coordinates $(z, w)$ on a neighbourhood of a fast plane in which the plane is $\mathbb{C} \times \{0\}$, the almost complex structure is standard along the plane and asymptotically cylindrical at $\infty$, and the spectral data of the asymptotic orbit are those of the loop $S_\infty$, with windings shifted by one. It lets statements about $\bar J$-holomorphic planes near $\mathbb{C} \times \{0\}$ for a standard tube structure, which involve no Reeb dynamics, be applied near a fast plane.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6 (Lemmas 6.10, 6.20); asymptotic operators and windings as in H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II, GAFA 5 (1995)

import Definitions.Def_FiniteEnergyPlane_Tube

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A standard tube around a fast plane. Let `u` be a fast finite-energy plane with a
nondegenerate end at `P`. Then there are `ρ, b > 0`, a smooth map `Φ : ℂ × ℂ → V 1` with
`Φ(z, 0) = u z`, and a standard tube structure `(Jbar, Jinf, Sinf)` of width `ρ` and rate `b`
such that on `ℂ × ball 0 ρ` the map `Φ` avoids `0`, has injective derivative and satisfies
`DΦ ∘ Jbar = J̃(Φ) ∘ DΦ`. Moreover `DΦ(0, 0)(τ, 1) = u 0` for some `τ`; in cylindrical
coordinates `aCoord (Φ) - T s - d - α(t, w)` and `proj (Φ) - X(t, w)` decay exponentially in
`C^∞`, uniformly in `w`, for `1`-periodic smooth `α`, `X` with `α(t, 0) = 0` and
`X(t, 0) = x(T t + c)`; every eigenvalue of the loop operator of `Sinf` is an eigenvalue of the
asymptotic operator of `P`; and an eigenvalue of winding `k` for `Sinf` has winding `k + 1`
for `P`. -/
theorem exists_stdTube_of_isFastPlane (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ ρ > 0, ∃ b > 0, ∃ (Φ : ℂ × ℂ → V 1) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
      (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Sinf : ℝ → CauchyRiemannIndex.Mat 1),
      IsStdTubeStructure ρ b Jbar Jinf Sinf ∧ ContDiff ℝ ∞ Φ ∧ (∀ z, Φ (z, 0) = u z) ∧
      (∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, Φ p ≠ 0 ∧ Function.Injective (fderiv ℝ Φ p) ∧
        (fderiv ℝ Φ p).comp (Jbar p) = (Jtilde H J (Φ p)).comp (fderiv ℝ Φ p)) ∧
      (∃ τ : ℂ, fderiv ℝ Φ (0, 0) (τ, 1) = u 0) ∧
      (∃ (d c : ℝ) (α : ℝ × ℂ → ℝ) (X : ℝ × ℂ → V 1),
        ContDiffOn ℝ ∞ α (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        ContDiffOn ℝ ∞ X (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        (∀ (t : ℝ) (w : ℂ), α (t + 1, w) = α (t, w) ∧ X (t + 1, w) = X (t, w)) ∧
        (∀ t : ℝ, α (t, 0) = 0 ∧ X (t, 0) = P.x (P.T * t + c)) ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          aCoord H (Φ (cylInf q.1 q.2.1, q.2.2)) - P.T * q.1 - d - α (q.2.1, q.2.2)) ρ b ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          proj H (Φ (cylInf q.1 q.2.1, q.2.2)) - X (q.2.1, q.2.2)) ρ b) ∧
      (∀ (μ : ℝ) e, IsLoopEigen Sinf μ e → ∃ v, IsAsymptoticEigen J P μ v) ∧
      (∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k → HasEigenWind J P μ (k + 1)) := by
  sorry

end FiniteEnergyPlane
