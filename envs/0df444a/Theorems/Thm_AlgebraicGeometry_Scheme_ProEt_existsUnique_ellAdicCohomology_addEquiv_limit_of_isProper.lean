-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_ProEt_existsUnique_ellAdicCohomology_addEquiv_limit_of_isProper
-- name    : AlgebraicGeometry.Scheme.ProEt.existsUnique_ellAdicCohomology_addEquiv_limit_of_isProper
-- status  : Open
-- author  : @Idealson
-- created : 2026-11-26T13:45:30.832714+00:00
-- url     : https://prove2.me/theorems/abe84709-78dd-40ce-a746-4f841c43cde5
-- title:
--   $\ell$-adic cohomology of a proper scheme over a separably closed field is the inverse limit of its étale cohomology with $\mathbb{Z}/\ell^n$-coefficients
-- statement:
--   Let $X$ be a scheme. Its **pro-étale site** $X_{\text{proét}}$ is the category of weakly étale $X$-schemes with the pro-étale topology, and $X_{\text{ét}}$ is its small étale site. Assume $X$ is proper over a separably closed field $K$, and let $\ell$ be a prime. As for the goal of the mission, the $\ell$-adic cohomology $H^m(X_{\text{proét}}, \mathbb Z_\ell)$ (cohomology of the sheaf of continuous $\mathbb Z_\ell$-valued functions), the pro-étale cohomology $H^m(X_{\text{proét}}, \mathbb Z/\ell^n)$ and the étale cohomology $H^m(X_{\text{ét}}, \mathbb Z/\ell^n)$ are related by canonical maps
--
--   $$
--   H^m\bigl(X_{\text{proét}}, \mathbb Z_\ell\bigr) \xrightarrow{\ \rho\ } \varprojlim_n H^m\bigl(X_{\text{proét}}, \mathbb Z/\ell^n\bigr) \xleftarrow{\ \lim c\ } \varprojlim_n H^m\bigl(X_{\text{ét}}, \mathbb Z/\ell^n\bigr).
--   $$
--
--   Then for every $i \ge 0$ there is a unique isomorphism of abelian groups
--
--   $$
--   e : H^{i+1}\bigl(X_{\text{proét}}, \mathbb Z_\ell\bigr) \xrightarrow{\ \sim\ } \varprojlim_n H^{i+1}\bigl(X_{\text{ét}}, \mathbb Z/\ell^n\bigr)
--   \qquad\text{such that}\qquad (\lim c) \circ e = \rho,
--   $$
--
--   with no finiteness hypothesis.
--
--   This is the unconditional form of the goal in the geometric situation the paper starts from: there the classical definition of $\ell$-adic cohomology as an inverse limit and the cohomology of the sheaf $\mathbb Z_\ell$ on the pro-étale site agree.
--
--   **Formalization Note** The paper's sentence concerns a variety over an algebraically closed field, a prime $\ell$ different from the characteristic, and $\mathbb Q_\ell$-coefficients. The Lean statement is for proper schemes over a separably closed field, any prime $\ell$, $\mathbb Z_\ell$-coefficients and degrees $\ge 1$; non-proper varieties, the passage to $\mathbb Q_\ell$ and degree $0$ are not covered. It follows from the goal and the finiteness statement for proper schemes.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Introduction, the identification asserted after Definition 1.1 (p. 2 of the arXiv v2 PDF), in integral form and for proper schemes; it combines the mission goal with M. Artin, SGA 4, Exposé XIV, Théorème de finitude pour un morphisme propre, Corollaire 1.2, https://grothendiecksga.com/read/sga4/en/XIV-1.html.

import Mathlib
import Definitions.Def_ProEtale_Comparator_Definitions

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe u
open CategoryTheory Limits Opposite Abelian
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProEt

theorem AlgebraicGeometry.Scheme.ProEt.existsUnique_ellAdicCohomology_addEquiv_limit_of_isProper (K : Type u) [Field K] [IsSepClosed K] (X : Scheme.{u}) (π : X ⟶ Spec (.of K)) [IsProper π] (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) :
    ∃! e : X.EllAdicCohomology ℓ (i + 1) ≃+
        ↥(limit (EllAdicEtaleComparison.etaleCohomologySystem X ℓ (i + 1))),
      ∀ x, ConcreteCategory.hom (limMap
          (EllAdicEtaleComparison.etaleToProetaleCohomologySystemHom X ℓ (i + 1)))
          (e x) =
        ConcreteCategory.hom
          (EllAdicEtaleComparison.ellAdicCohomologyToLimit X ℓ (i + 1)) x := by sorry
