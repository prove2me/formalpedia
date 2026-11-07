-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_fastPlane_slice_family
-- name    : FiniteEnergyPlane.exists_fastPlane_slice_family
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-06T10:48:43.579526+00:00
-- url     : https://prove2.me/theorems/82feda14-efe7-47ae-b95a-6f527aae76c4
-- title:
--   One-parameter family of fast planes transverse to translations
-- statement:
--   Let $S = H^{-1}(1) \subset V_1 = \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on $\xi$, and let $P$ be a periodic Reeb orbit on $S$ whose Conley–Zehnder index is at least $3$. Let $u$ be an embedded fast finite-energy plane asymptotic to $P$ at $\infty$. Then for every $l \ge 1$ there are $r > 0$ and a $C^l$ map $g : \mathbb{C} \times (-r, r) \to V_1$ such that:
--
--   1. $g(\cdot, 0) = u$;
--   2. every $g(\cdot, t)$, $|t| < r$, is a fast finite-energy plane asymptotic to $P$ at $\infty$;
--   3. the map $(z, c, t) \mapsto c \cdot g(z, t) = e^{2c} g(z, t)$ is injective on $\mathbb{C} \times (-r, r) \times (-r, r)$;
--   4. this map has injective derivative everywhere: if $Dg(z, t)(\Delta, \delta t) + \lambda\, g(z, t) = 0$ with $\Delta \in \mathbb{C}$ and $\delta t, \lambda \in \mathbb{R}$, then $\Delta = 0$, $\delta t = 0$ and $\lambda = 0$.
--
--   Thus the planes $g(\cdot, t)$ form a one-parameter family through $u$ that is transverse to the $\mathbb{R}$-translations in the symplectization, and the small translates of its members are pairwise disjoint. This is the geometric content of Hryniewicz, *Fast finite-energy planes in symplectizations and applications*, Trans. AMS 364 (2012), Lemmas 6.10 and 6.20, written in a form where the $\mathbb{R}$-translation parameter is explicit.
--
--   Formalization Note: $V_1 \setminus \{0\}$ is the model of the symplectization $\mathbb{R} \times S$, in which the translation by $c$ is $y \mapsto e^{2c} y$. Item 4 is the injectivity of the derivative of the map in item 3 at $(z, c, t)$, after dividing by $e^{2c}$ and writing $\lambda = 2\,\delta c$. Since the map $g$ is only asserted to be $C^l$ on the open set $\mathbb{C} \times (-r, r)$, no uniformity as $|z| \to \infty$ is part of the statement. Non-vacuity: for the round sphere with $J = i$, $g(z, t) = (z, e^{it})$ satisfies the conclusion for $u(z) = (z, 1)$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Lemmas 6.10 and 6.20, Theorem 2.3; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations III: Fredholm theory, Birkhäuser (1999)

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A one-parameter family of fast planes through an embedded fast plane, transverse to the
`ℝ`-translations. Let `u` be an embedded fast finite-energy plane asymptotic to `P` at `∞`, where
the Conley–Zehnder index of `P` is at least `3`. Then for every `l ≥ 1` there are `r > 0` and a
`C^l` map `g : ℂ × (-r, r) → V 1` with `g(·, 0) = u` such that every `g(·, t)` is a fast
finite-energy plane asymptotic to `P` at `∞`, and such that
`(z, c, t) ↦ c · g(z, t) = e^{2c} • g(z, t)` is injective on `ℂ × (-r, r) × (-r, r)` with injective
derivative. The latter is stated at `c = 0`: `D g(z, t)(Δ, δt) + λ • g(z, t) = 0` forces
`Δ = 0`, `δt = 0` and `λ = 0`. -/
theorem exists_fastPlane_slice_family (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) (l : ℕ) (hl : 1 ≤ l) :
    ∃ r > 0, ∃ g : ℂ × ℝ → V 1, ContDiffOn ℝ l g (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, g (z, 0) = u z) ∧
      (∀ t ∈ Set.Ioo (-r) r, IsFastPlane H J (fun z => g (z, t)) ∧
        IsNondegenerateEnd H (fun z => g (z, t)) cylInf P 1) ∧
      Set.InjOn (fun q : ℂ × ℝ × ℝ => Real.exp (2 * q.2.1) • g (q.1, q.2.2))
        (Set.univ ×ˢ (Set.Ioo (-r) r ×ˢ Set.Ioo (-r) r)) ∧
      ∀ z, ∀ t ∈ Set.Ioo (-r) r, ∀ (Δ : ℂ) (δt lam : ℝ),
        fderiv ℝ g (z, t) (Δ, δt) + lam • g (z, t) = 0 → Δ = 0 ∧ δt = 0 ∧ lam = 0 := by
  sorry

end FiniteEnergyPlane
