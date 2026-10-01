-- Prove2me | Theorems.Thm_AlbouyKaloshin_theorem6_five_body_complex_finite
-- name    : AlbouyKaloshin.theorem6_five_body_complex_finite
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T22:10:46.016753+00:00
-- url     : https://prove2.me/theorems/174c2b2d-d835-4f33-ba02-d53a52f94e65
-- title:
--   Theorem 6: five bodies, finitely many complex normalized central configurations for generic masses
-- statement:
--   There is a closed algebraic subset $A\subset\mathbb R^5$ of the mass space, of codimension at least $2$, such that for every $(m_1,\dots,m_5)\in(\mathbb R_{>0})^5\setminus A$ the planar five-body problem has finitely many normalized central configurations, i.e. system (4) with $n=5$ has finitely many complex solutions.
--
--   This is the stronger form of the main Theorem 2, from which Theorem 2 follows.
--
--   **Formalization Note** $A$ is the real zero locus of an ideal $I\subseteq\mathbb R[m_1,\dots,m_5]$, and "codimension at least $2$" is expressed as $\dim_{\mathrm{Krull}}\mathbb R[m_1,\dots,m_5]/I\le3$.
-- source:
--   A. Albouy and V. Kaloshin, Finiteness of central configurations of five bodies in the plane, Annals of Mathematics 176 (2012), no. 1, 535–588, https://doi.org/10.4007/annals.2012.176.1.10, p. 581, Theorem 6

import Mathlib
import Definitions.Def_AlbouyKaloshin_CentralConfigurations

namespace AlbouyKaloshin

theorem theorem6_five_body_complex_finite :
    ∃ I : Ideal (MvPolynomial (Fin 5) ℝ),
      ringKrullDim (MvPolynomial (Fin 5) ℝ ⧸ I) ≤ 3 ∧
      ∀ m : Fin 5 → ℝ, (∀ k, 0 < m k) → m ∉ massZeroLocus I →
        (NormalizedCC 5 (fun k => (m k : ℂ))).Finite := by sorry

end AlbouyKaloshin
