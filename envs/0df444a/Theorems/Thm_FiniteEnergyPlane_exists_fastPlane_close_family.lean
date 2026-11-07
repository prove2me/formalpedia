-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_fastPlane_close_family
-- name    : FiniteEnergyPlane.exists_fastPlane_close_family
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-06T11:24:58.026469+00:00
-- url     : https://prove2.me/theorems/07df3997-506e-4b90-8b60-3af8530b6560
-- title:
--   A family of embedded fast planes uniformly close to a given one
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on the contact planes, and let $P$ be a periodic Reeb orbit whose Conley–Zehnder index is at least $3$ (`P.IsCZAtLeast 3`; $P$ may be degenerate). Let $u$ be an embedded fast finite-energy plane asymptotic to $P$ at $\infty$.
--
--   Then for every integer $l \ge 1$ and every $\varepsilon > 0$ there are $r > 0$ and a $C^l$ map $g : \mathbb{C} \times (-r, r) \to V_1$ with $g(\cdot, 0) = u$ such that:
--
--   1. for every $t \in (-r, r)$, the map $g(\cdot, t)$ is an embedded fast finite-energy plane asymptotic to $P$ at $\infty$, and it is $\varepsilon$-close to $u$ in the sense of `IsCylCloseTo`;
--   2. the images of the translates $e^{2c} g(\cdot, t)$, $(c, t) \in (-r, r)^2$, are pairwise different: equal images force equal parameters;
--   3. for all $z$ and all $t \in (-r, r)$, the identity $Dg(z, t)(\Delta, \delta t) + \lambda\, g(z, t) = 0$ forces $\Delta = 0$, $\delta t = 0$ and $\lambda = 0$.
--
--   Clause 3 says that the plane $g(\cdot,t)$, the parameter direction and the $\mathbb{R}$-translation direction together span the tangent space at every point of every member.
--
--   **Role.** Together with the companion statement on the images of nearby fast planes, this yields a family of fast planes whose translates are pairwise disjoint, as in Hryniewicz (Trans. AMS 2012), Lemma 6.10 and Lemma 6.20.
--
--   **Formalization Note.** The symplectization $\mathbb{R} \times S$ is $V_1 \setminus \{0\}$, and the translation $c \cdot u$ is $e^{2c} u$ (`shiftA`). Clause 3 is stated at $c = 0$; the translates are scalar multiples of the members. Regularity in $(z, t)$ is `ContDiffOn` on $\mathbb{C} \times (-r, r)$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemma 6.10 and Lemma 6.20; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectizations III, Fredholm theory (1999), Theorem 1.5

import Definitions.Def_FiniteEnergyPlane_CylClose

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A one-parameter family of embedded fast planes through an embedded fast plane, uniformly close
to it. Let `u` be an embedded fast finite-energy plane asymptotic to `P` at `∞`, where the
Conley–Zehnder index of `P` is at least `3`. Then for every `l ≥ 1` and `ε > 0` there are `r > 0`
and a `C^l` map `g : ℂ × (-r, r) → V 1` with `g(·, 0) = u` such that every `g(·, t)` is an embedded
fast finite-energy plane asymptotic to `P` at `∞` and `ε`-close to `u` in the sense of
`IsCylCloseTo`; the images of the translates `e^{2c} • g(·, t)`, `(c, t) ∈ (-r, r)²`, are pairwise
different; and `D g(z, t)(Δ, δt) + λ • g(z, t) = 0` forces `Δ = 0`, `δt = 0` and `λ = 0`. -/
theorem exists_fastPlane_close_family (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) (l : ℕ) (hl : 1 ≤ l) (ε : ℝ) (hε : 0 < ε) :
    ∃ r > 0, ∃ g : ℂ × ℝ → V 1, ContDiffOn ℝ l g (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, g (z, 0) = u z) ∧
      (∀ t ∈ Set.Ioo (-r) r, IsFastPlane H J (fun z => g (z, t)) ∧
        IsNondegenerateEnd H (fun z => g (z, t)) cylInf P 1 ∧
        IsEmbeddedPlane (fun z => g (z, t)) ∧ IsCylCloseTo H ε (fun z => g (z, t)) u) ∧
      (∀ c ∈ Set.Ioo (-r) r, ∀ t ∈ Set.Ioo (-r) r, ∀ c' ∈ Set.Ioo (-r) r, ∀ t' ∈ Set.Ioo (-r) r,
        Set.range (shiftA c (fun z => g (z, t))) = Set.range (shiftA c' (fun z => g (z, t'))) →
          c = c' ∧ t = t') ∧
      ∀ z, ∀ t ∈ Set.Ioo (-r) r, ∀ (Δ : ℂ) (δt lam : ℝ),
        fderiv ℝ g (z, t) (Δ, δt) + lam • g (z, t) = 0 → Δ = 0 ∧ δt = 0 ∧ lam = 0 := by
  sorry

end FiniteEnergyPlane
