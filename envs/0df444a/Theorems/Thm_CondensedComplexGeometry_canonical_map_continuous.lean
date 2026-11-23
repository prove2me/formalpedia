-- Prove2me | Theorems.Thm_CondensedComplexGeometry_canonical_map_continuous
-- name    : CondensedComplexGeometry.canonical_map_continuous
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T01:42:54.762134+00:00
-- url     : https://prove2.me/theorems/59097c5a-6137-4174-8de9-7d548551c77a
-- title:
--   Continuity of the canonical map from characters to the Berkovich spectrum
-- statement:
--   A topological step toward **Ostrowski's theorem** (Theorem 5.11 of Clausen–Scholze). Let $R$ be a commutative $\mathbb C$-algebra. The canonical map
--
--   $$\operatorname{Hom}_{\mathbb C}(R,\mathbb C)\ \longrightarrow\ \mathcal M_{\mathrm{Berk}}(R),\qquad f\ \longmapsto\ \big(x\mapsto |f(x)|_{\mathbb C}\big)$$
--
--   is well defined (the function $x\mapsto|f(x)|_{\mathbb C}$ is a bounded multiplicative seminorm) and is **continuous** for the pointwise-convergence topologies on both sides.
--
--   Together with the algebraic representation (which gives the bijection) and continuity of the inverse, this yields the homeomorphism $\mathcal M_{\mathrm{Berk}}(R)\cong\operatorname{Hom}_{\mathbb C}(R,\mathbb C)$.
--
--   **Formalization Note.** Stated as the existence of a continuous map `g : ↥(ComplexCharacters R) → ↥(BerkovichSpectrum R)` whose underlying seminorm satisfies `((g f).1 x : ℝ) = ‖f.1 x‖`; continuity is with respect to the subspace topologies inherited from the Pi topologies on `R → ℂ` and `R → ℝ≥0`.
-- source:
--   D. Clausen, P. Scholze, Condensed Mathematics and Complex Geometry, lecture notes (Summer 2022, rev. May 2026), https://people.mpim-bonn.mpg.de/scholze/Complex.pdf, p. 56, Theorem 5.11 (Ostrowski).

import Mathlib
import Definitions.Def_CondensedComplexGeometry_berkovich

namespace CondensedComplexGeometry

theorem canonical_map_continuous (R : Type*) [CommRing R] [Algebra ℂ R] :
    ∃ (g : ↥(ComplexCharacters R) → ↥(BerkovichSpectrum R)),
      Continuous g ∧ ∀ (f : ↥(ComplexCharacters R)) (x : R),
        ((g f).1 x : ℝ) = ‖f.1 x‖ := by sorry

end CondensedComplexGeometry
