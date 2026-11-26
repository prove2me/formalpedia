-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_ProEt_bijective_etaleToProetaleCohomology
-- name    : AlgebraicGeometry.Scheme.ProEt.bijective_etaleToProetaleCohomology
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T12:46:57.276856+00:00
-- url     : https://prove2.me/theorems/35f6d97f-3432-5590-b5c6-d27674837abd
-- title:
--   Étale and pro-étale cohomology with $\mathbb{Z}/\ell^n$-coefficients agree
-- statement:
--   Let $X$ be a scheme. Its **pro-étale site** $X_{\text{proét}}$ is the category of weakly étale $X$-schemes with the pro-étale topology, and $X_{\text{ét}}$ is its small étale site. Let $\ell$ be a natural number and $m, n \ge 0$. On $X_{\text{ét}}$ consider the constant sheaf $\mathbb Z/\ell^n$, and on $X_{\text{proét}}$ the sheaf $U \mapsto \operatorname{Map}_{\mathrm{cont}}(U, \mathbb Z/\ell^n)$ of continuous functions to the discrete group $\mathbb Z/\ell^n$. Pullback along $\nu$, followed by the canonical map from the pulled-back constant sheaf to the sheaf of continuous functions, gives a comparison map
--
--   $$
--   c : H^m\bigl(X_{\text{ét}}, \mathbb Z/\ell^n\bigr) \longrightarrow H^m\bigl(X_{\text{proét}}, \mathbb Z/\ell^n\bigr).
--   $$
--
--   This map is bijective, for every scheme $X$ and all $m$, $n$.
--
--   It is the levelwise comparison used to pass from the pro-étale side to the étale side in the description of $\ell$-adic cohomology as an inverse limit.
--
--   **Formalization Note** The two sides are the values at $n$ of the inverse systems `etaleCohomologySystem X ℓ m` and `proetaleCohomologySystem X ℓ m`, and $c$ is the component at $n$ of `etaleToProetaleCohomologySystemHom X ℓ m`. No primality hypothesis on $\ell$ is needed here.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Not a numbered result of the paper: consequence of Corollary 5.1.6 and Lemma 4.2.12(3). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/EllAdicCanonical.lean, lines 174-198 (`AlgebraicGeometry.Scheme.ProEt.bijective_etaleToProetaleCohomology`).

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

theorem AlgebraicGeometry.Scheme.ProEt.bijective_etaleToProetaleCohomology (ℓ m n : ℕ) :
    Function.Bijective (ConcreteCategory.hom
      ((EllAdicEtaleComparison.etaleToProetaleCohomologySystemHom X ℓ m).app (op n))) := by sorry
