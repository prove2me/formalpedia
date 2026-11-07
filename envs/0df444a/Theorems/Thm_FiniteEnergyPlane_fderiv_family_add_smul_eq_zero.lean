-- Prove2me | Theorems.Thm_FiniteEnergyPlane_fderiv_family_add_smul_eq_zero
-- name    : FiniteEnergyPlane.fderiv_family_add_smul_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T15:15:05.352214+00:00
-- url     : https://prove2.me/theorems/905957c7-e9fe-4de2-a350-99ecb1a7410d
-- title:
--   Transversality of a J-holomorphic family at one point holds along a fast member
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on the contact planes, and let $P$ be a periodic Reeb orbit. Let $\delta < 0$ be such that every eigenvalue of the asymptotic operator $A_P$ below $\delta$ has winding number at most $1$ and every eigenvalue above $\delta$ has winding number at least $2$, in the global frame of $\xi$. Let $g : \mathbb{C} \times (-r, r) \to V_1$ be $C^2$ with every $g(\cdot, t')$ $\tilde J$-holomorphic, and let $t \in (-r, r)$ be such that $g(\cdot, t)$ is a fast finite-energy plane asymptotic to $P$ at $\infty$, $\partial_t g(\cdot, t)$ is smooth, and for some $C$ and every $z$ some $\Delta \in \mathbb{C}$ has $|Dg(z, t)(\Delta, 1)| \le C (1 + |z|)^{\delta/2\pi} |g(z, t)|$.
--
--   If the identity $Dg(0, t)(\Delta, \delta t) + \lambda\, g(0, t) = 0$ forces $\Delta = 0$, $\delta t = 0$ and $\lambda = 0$, then for every $z \in \mathbb{C}$ the identity $Dg(z, t)(\Delta, \delta t) + \lambda\, g(z, t) = 0$ forces the same.
--
--   **Role.** The tangent plane of the member, the parameter direction and the $\mathbb{R}$-translation direction then span $T V_1$ at every point of the member, not only at $z = 0$.
--
--   **Formalization Note.** The symplectization $\mathbb{R} \times S$ is $V_1 \setminus \{0\}$, with $y = e^{2a} x$, $a$ = `aCoord H y` and $x$ = `proj H y`. Winding numbers are `HasEigenWind`; $(1 + |z|)^{\delta/2\pi}$ is the cylindrical weight $e^{\delta s}$ for $|z| = e^{2\pi s}$. The bound measures the $t$-derivative modulo the tangent plane of the member, relative to $|g|$. The point $z = 0$ is only a convenient base point.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemma 6.10 and Lemma 6.20

import Definitions.Def_FiniteEnergyPlane_CylClose

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Transversality of a family of `J̃`-holomorphic maps at one point of a fast member holds along the
whole member. Let `δ < 0` be such that every eigenvalue of `A_P` below `δ` has winding number at most
`1` and every eigenvalue above `δ` has winding number at least `2`. Let `g : ℂ × (-r, r) → V 1` be
`C²` with every `g(·, t')` `J̃`-holomorphic, and let `g(·, t)` be a fast finite-energy plane
asymptotic to `P` at `∞`, with `∂ₜg(·, t)` smooth and with `Δ` at each `z` such that
`‖Dg(z, t)(Δ, 1)‖ ≤ C (1 + ‖z‖)^{δ/2π} ‖g(z, t)‖`. If `Dg(0, t)(Δ, δt) + λ • g(0, t) = 0` forces
`Δ = 0`, `δt = 0`, `λ = 0`, then the same holds with `0` replaced by any `z`. -/
theorem fderiv_family_add_smul_eq_zero (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (δ : ℝ) (hδ : δ < 0)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k))
    (r : ℝ) (g : ℂ × ℝ → V 1) (hg : ContDiffOn ℝ 2 g (Set.univ ×ˢ Set.Ioo (-r) r))
    (hgJ : ∀ t' ∈ Set.Ioo (-r) r,
      JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ (fun z => g (z, t')))
    (t : ℝ) (ht : t ∈ Set.Ioo (-r) r)
    (hfast : IsFastPlane H J (fun z => g (z, t)))
    (hend : IsNondegenerateEnd H (fun z => g (z, t)) cylInf P 1)
    (hX : ContDiff ℝ ∞ (fun z => fderiv ℝ g (z, t) (0, 1)))
    (C : ℝ) (hrate : ∀ z, ∃ Δ : ℂ, ‖fderiv ℝ g (z, t) (Δ, 1)‖ ≤
      C * (1 + ‖z‖) ^ (δ / (2 * π)) * ‖g (z, t)‖)
    (htr : ∀ (Δ : ℂ) (δt lam : ℝ), fderiv ℝ g (0, t) (Δ, δt) + lam • g (0, t) = 0 →
      Δ = 0 ∧ δt = 0 ∧ lam = 0) (z : ℂ) (Δ : ℂ) (δt lam : ℝ)
    (h0 : fderiv ℝ g (z, t) (Δ, δt) + lam • g (z, t) = 0) :
    Δ = 0 ∧ δt = 0 ∧ lam = 0 := by
  sorry

end FiniteEnergyPlane
