-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isEmbeddedPlane_of_isCylCloseTo
-- name    : FiniteEnergyPlane.isEmbeddedPlane_of_isCylCloseTo
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T15:14:56.587697+00:00
-- url     : https://prove2.me/theorems/634c8c05-92bc-4d60-adec-47e6e406990d
-- title:
--   Maps close to an embedded fast plane are embedded
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on the contact planes, and let $P$ be a periodic Reeb orbit. Let $u$ be an embedded fast finite-energy plane asymptotic to $P$ at $\infty$.
--
--   Then there is $\varepsilon > 0$ such that every $C^1$ map $f : \mathbb{C} \to V_1$ that avoids $0$ and is $\varepsilon$-close to $u$ in the sense of `IsCylCloseTo` is an embedded plane: $f$ is injective and $Df(z)$ is injective at every $z$.
--
--   **Role.** Embeddedness is thus open among planes in the uniform cylindrical $C^1$ sense, including near $\infty$. It makes every member of a family close to $u$ embedded.
--
--   **Formalization Note.** $f$ need not be $\tilde J$-holomorphic and need not be asymptotic to $P$. $P$ is not assumed prime in the statement; it is the asymptotic limit of the fast plane $u$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemma 6.10 and Lemma 6.20

import Definitions.Def_FiniteEnergyPlane_CylClose

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Maps close to an embedded fast plane are embedded. Let `u` be an embedded fast finite-energy
plane asymptotic to `P` at `∞`. Then there is `ε > 0` such that every `C¹` map `f : ℂ → V 1` that
avoids `0` and is `ε`-close to `u` in the sense of `IsCylCloseTo` is an embedded plane. -/
theorem isEmbeddedPlane_of_isCylCloseTo (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) :
    ∃ ε > 0, ∀ f : ℂ → V 1, ContDiff ℝ 1 f → (∀ z, f z ≠ 0) → IsCylCloseTo H ε f u →
      IsEmbeddedPlane f := by
  sorry

end FiniteEnergyPlane
