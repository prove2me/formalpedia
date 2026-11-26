-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_ProEt_bijective_ellAdicCohomologyToLimit_of_finite
-- name    : AlgebraicGeometry.Scheme.ProEt.bijective_ellAdicCohomologyToLimit_of_finite
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T12:49:13.211001+00:00
-- url     : https://prove2.me/theorems/9f12cba0-c140-5482-9888-2819da16dde4
-- title:
--   $\ell$-adic cohomology is the inverse limit of pro-étale cohomology with $\mathbb{Z}/\ell^n$-coefficients, under finiteness
-- statement:
--   Let $X$ be a scheme. Its **pro-étale site** $X_{\text{proét}}$ is the category of weakly étale $X$-schemes with the pro-étale topology, and $X_{\text{ét}}$ is its small étale site. Let $\ell$ be a prime. The $\ell$-adic cohomology $H^m(X_{\text{proét}}, \mathbb Z_\ell)$ is the cohomology of the sheaf $U \mapsto \operatorname{Map}_{\mathrm{cont}}(U, \mathbb Z_\ell)$ on $X_{\text{proét}}$. Reduction $\mathbb Z_\ell \to \mathbb Z/\ell^n$ induces a canonical map
--
--   $$
--   \rho : H^m\bigl(X_{\text{proét}}, \mathbb Z_\ell\bigr) \longrightarrow \varprojlim_n H^m\bigl(X_{\text{proét}}, \mathbb Z/\ell^n\bigr).
--   $$
--
--   Let $i \ge 0$ and suppose the étale cohomology groups $H^i(X_{\text{ét}}, \mathbb Z/\ell^n)$ are finite for all $n$. Then $\rho$ is bijective in degree $m = i + 1$.
--
--   In general the two sides differ by a $\varprojlim^1$ term built from the groups one degree lower (Jannsen); the finiteness hypothesis is what makes that term vanish.
--
--   **Formalization Note** $H^m(X_{\text{proét}}, \mathbb Z_\ell)$ is Mathlib's `X.EllAdicCohomology ℓ m`, $\rho$ is `ellAdicCohomologyToLimit X ℓ (i + 1)`, and the hypothesis is finiteness of every term of `etaleCohomologySystem X ℓ i`. The statement concerns degrees $\ge 1$ only.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Not a numbered result of the paper. Ingredients: Proposition 5.6.2, Lemma 6.8.2(1); U. Jannsen, Continuous étale cohomology, Math. Ann. 280 (1988), §1, https://doi.org/10.1007/BF01456052. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/EllAdicCanonical.lean, lines 257-302 (`AlgebraicGeometry.Scheme.ProEt.bijective_ellAdicCohomologyToLimit_of_finite`).

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

theorem AlgebraicGeometry.Scheme.ProEt.bijective_ellAdicCohomologyToLimit_of_finite (i : ℕ)
    (hfin : ∀ n : ℕ, Finite (ToType
      ((EllAdicEtaleComparison.etaleCohomologySystem X ℓ i).obj (op n)))) :
    Function.Bijective (ConcreteCategory.hom
      (EllAdicEtaleComparison.ellAdicCohomologyToLimit X ℓ (i + 1))) := by sorry
