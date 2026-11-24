-- Prove2me | Theorems.Thm_CondensedComplexGeometry_ostrowski
-- name    : CondensedComplexGeometry.ostrowski
-- status  : Proved
-- author  : @LG
-- created : 2026-11-23T01:43:36.342894+00:00
-- url     : https://prove2.me/theorems/24e2d7e6-99b3-4ad7-95e6-30140fa7541b
-- title:
--   Ostrowski's theorem: Berkovich spectrum of a complex algebra equals its classical points
-- statement:
--   **Ostrowski's theorem** (Theorem 5.11 of Clausen–Scholze, *Condensed Mathematics and Complex Geometry*). Let $R$ be any commutative $\mathbb C$-algebra. Every bounded multiplicative seminorm $|\cdot|\in\mathcal M_{\mathrm{Berk}}(R)$ is of the form
--
--   $$|x| = |f(x)|_{\mathbb C}\qquad(x\in R)$$
--
--   for a **unique** $\mathbb C$-algebra homomorphism $f:R\to\mathbb C$, and the resulting bijection is a homeomorphism
--
--   $$\mathcal M_{\mathrm{Berk}}(R)\ \cong\ \operatorname{Hom}_{\mathbb C}(R,\mathbb C),$$
--
--   where both sides carry the topology of pointwise convergence (the subspace topology from $\prod_{x\in R}\mathbb R_{\ge 0}$ and $\prod_{x\in R}\mathbb C$ respectively).
--
--   This is the archimedean rigidity statement that identifies the Berkovich spectrum of a complex algebra with its classical points; it is the input that makes the course's analysis-free construction of the holomorphic structure sheaf work, and a form of the Gelfand–Mazur theorem. Unlike the Banach-algebra Gelfand–Mazur theorem, no norm or completeness is assumed on $R$.
--
--   **Formalization Note.** The homeomorphism is stated as the existence of `e : ↥(BerkovichSpectrum R) ≃ₜ ↥(ComplexCharacters R)` such that each seminorm `v` satisfies `(v.1 x : ℝ) = ‖(e v).1 x‖`; the bijectivity of `e` encodes the existence and uniqueness of the representing homomorphism.
-- source:
--   D. Clausen, P. Scholze, Condensed Mathematics and Complex Geometry, lecture notes (Summer 2022, rev. May 2026), https://people.mpim-bonn.mpg.de/scholze/Complex.pdf, p. 56, Theorem 5.11 (Ostrowski).

import Mathlib
import Definitions.Def_CondensedComplexGeometry_berkovich

namespace CondensedComplexGeometry

theorem ostrowski (R : Type*) [CommRing R] [Algebra ℂ R] :
    ∃ (e : ↥(BerkovichSpectrum R) ≃ₜ ↥(ComplexCharacters R)),
      ∀ (v : ↥(BerkovichSpectrum R)) (x : R), (v.1 x : ℝ) = ‖(e v).1 x‖ := by sorry

end CondensedComplexGeometry
