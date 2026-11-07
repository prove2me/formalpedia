-- Prove2me | Theorems.Thm_FiniteEnergyPlane_range_eq_or_disjoint_of_isCylCloseTo
-- name    : FiniteEnergyPlane.range_eq_or_disjoint_of_isCylCloseTo
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-06T11:24:56.618051+00:00
-- url     : https://prove2.me/theorems/a0ea0079-621c-4191-8a1e-57f82664a8e7
-- title:
--   Images of fast planes near a given embedded fast plane are equal or disjoint
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on the contact planes, and let $P$ be a periodic Reeb orbit whose Conley–Zehnder index is at least $3$ (`P.IsCZAtLeast 3`; $P$ may be degenerate). Let $u$ be an embedded fast finite-energy plane asymptotic to $P$ at $\infty$.
--
--   Then there is $\varepsilon > 0$ such that any two fast finite-energy planes $f_1, f_2$ asymptotic to $P$ at $\infty$ that are $\varepsilon$-close to $u$ in the sense of `IsCylCloseTo` satisfy
--
--   $$f_1(\mathbb{C}) = f_2(\mathbb{C}) \quad\text{or}\quad f_1(\mathbb{C}) \cap f_2(\mathbb{C}) = \emptyset$$
--
--   as subsets of the symplectization.
--
--   **Role.** This is a local form, near a fixed plane and in $\mathbb{R} \times S$, of the dichotomy for the images of fast planes in Hryniewicz (Trans. AMS 2012), Lemma 6.23. It does not assume that $f_1$ or $f_2$ is embedded, nor that their components in $S$ avoid the orbit.
--
--   **Formalization Note.** The symplectization $\mathbb{R} \times S$ is $V_1 \setminus \{0\}$, so the images are compared as subsets of $V_1$. No relation between the parametrizations of $f_1$ and $f_2$ is asserted.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemma 6.23 and Section 6.3.8

import Definitions.Def_FiniteEnergyPlane_CylClose

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Fast planes close to an embedded fast plane have equal or disjoint images in the
symplectization. Let `u` be an embedded fast finite-energy plane asymptotic to `P` at `∞`, where the
Conley–Zehnder index of `P` is at least `3`. Then there is `ε > 0` such that any two fast
finite-energy planes asymptotic to `P` at `∞` that are `ε`-close to `u` in the sense of
`IsCylCloseTo` have equal or disjoint images in `V 1`. -/
theorem range_eq_or_disjoint_of_isCylCloseTo (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) :
    ∃ ε > 0, ∀ f₁ f₂ : ℂ → V 1,
      IsFastPlane H J f₁ → IsNondegenerateEnd H f₁ cylInf P 1 → IsCylCloseTo H ε f₁ u →
      IsFastPlane H J f₂ → IsNondegenerateEnd H f₂ cylInf P 1 → IsCylCloseTo H ε f₂ u →
      Set.range f₁ = Set.range f₂ ∨ Disjoint (Set.range f₁) (Set.range f₂) := by
  sorry

end FiniteEnergyPlane
