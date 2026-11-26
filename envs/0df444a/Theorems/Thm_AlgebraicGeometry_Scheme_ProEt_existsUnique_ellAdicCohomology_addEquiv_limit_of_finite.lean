-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_ProEt_existsUnique_ellAdicCohomology_addEquiv_limit_of_finite
-- name    : AlgebraicGeometry.Scheme.ProEt.existsUnique_ellAdicCohomology_addEquiv_limit_of_finite
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T12:52:24.045507+00:00
-- url     : https://prove2.me/theorems/aec75a68-6e8c-4b89-876e-1ee1ee21b19f
-- title:
--   $\ell$-adic cohomology is canonically the inverse limit of étale cohomology with $\mathbb{Z}/\ell^n$-coefficients
-- statement:
--   Let $X$ be a scheme. Its **pro-étale site** $X_{\text{proét}}$ is the category of weakly étale $X$-schemes with the pro-étale topology, and $X_{\text{ét}}$ is its small étale site. Let $\ell$ be a prime. Three families of groups are attached to $X$: the $\ell$-adic cohomology $H^m(X_{\text{proét}}, \mathbb Z_\ell)$, i.e. the cohomology of the sheaf of continuous $\mathbb Z_\ell$-valued functions on $X_{\text{proét}}$; the pro-étale cohomology $H^m(X_{\text{proét}}, \mathbb Z/\ell^n)$ of the sheaves of continuous $\mathbb Z/\ell^n$-valued functions; and the étale cohomology $H^m(X_{\text{ét}}, \mathbb Z/\ell^n)$ of the constant sheaves. They are related by two canonical maps
--
--   $$
--   H^m\bigl(X_{\text{proét}}, \mathbb Z_\ell\bigr) \xrightarrow{\ \rho\ } \varprojlim_n H^m\bigl(X_{\text{proét}}, \mathbb Z/\ell^n\bigr) \xleftarrow{\ \lim c\ } \varprojlim_n H^m\bigl(X_{\text{ét}}, \mathbb Z/\ell^n\bigr),
--   $$
--
--   where $\rho$ is induced by the reductions $\mathbb Z_\ell \to \mathbb Z/\ell^n$ and $c$ by pullback from the étale to the pro-étale site.
--
--   Let $i \ge 0$ and suppose $H^i(X_{\text{ét}}, \mathbb Z/\ell^n)$ is finite for every $n$. Then there exists a unique isomorphism of abelian groups
--
--   $$
--   e : H^{i+1}\bigl(X_{\text{proét}}, \mathbb Z_\ell\bigr) \xrightarrow{\ \sim\ } \varprojlim_n H^{i+1}\bigl(X_{\text{ét}}, \mathbb Z/\ell^n\bigr)
--   \qquad\text{such that}\qquad (\lim c) \circ e = \rho .
--   $$
--
--   This identifies the cohomology of an actual sheaf on the pro-étale site with the classical definition of $\ell$-adic cohomology as an inverse limit, in a form that pins the isomorphism down by its compatibility with the canonical maps.
--
--   **Formalization Note** $H^m(X_{\text{proét}}, \mathbb Z_\ell)$ is Mathlib's `X.EllAdicCohomology ℓ m`; the systems are `etaleCohomologySystem X ℓ m` and `proetaleCohomologySystem X ℓ m`, $\rho$ is `ellAdicCohomologyToLimit` and $c$ is `etaleToProetaleCohomologySystemHom`. There is no natural map between the two outer groups in either direction, which is why the statement is formulated through the zig-zag. The hypothesis is in degree $i$ and the conclusion in degree $i + 1$; degree $0$ is not covered.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Not a numbered result of the paper: integral form, under an explicit finiteness hypothesis, of the identification asserted in the Introduction after Definition 1.1 (p. 2 of the arXiv v2 PDF). Ingredients: Corollary 5.1.6, Proposition 5.6.2, Lemma 6.8.2(1); U. Jannsen, Continuous étale cohomology, Math. Ann. 280 (1988), §1, https://doi.org/10.1007/BF01456052. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/EllAdicCanonical.lean, lines 306-339 (`AlgebraicGeometry.Scheme.ProEt.existsUnique_ellAdicCohomology_addEquiv_limit_of_finite`).

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
variable (X : Scheme.{u})
variable (ℓ : ℕ) [Fact ℓ.Prime]

theorem AlgebraicGeometry.Scheme.ProEt.existsUnique_ellAdicCohomology_addEquiv_limit_of_finite (i : ℕ)
    (hfin : ∀ n : ℕ, Finite (ToType
      ((EllAdicEtaleComparison.etaleCohomologySystem X ℓ i).obj (op n)))) :
    ∃! e : X.EllAdicCohomology ℓ (i + 1) ≃+
        ↥(limit (EllAdicEtaleComparison.etaleCohomologySystem X ℓ (i + 1))),
      ∀ x, ConcreteCategory.hom (limMap
          (EllAdicEtaleComparison.etaleToProetaleCohomologySystemHom X ℓ (i + 1)))
          (e x) =
        ConcreteCategory.hom
          (EllAdicEtaleComparison.ellAdicCohomologyToLimit X ℓ (i + 1)) x := by sorry
