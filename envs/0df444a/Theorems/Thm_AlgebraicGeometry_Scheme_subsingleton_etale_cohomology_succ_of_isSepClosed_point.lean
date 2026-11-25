-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_subsingleton_etale_cohomology_succ_of_isSepClosed_point
-- name    : AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_succ_of_isSepClosed_point
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T16:21:02.325818+00:00
-- url     : https://prove2.me/theorems/b51cb515-5c2d-4357-a38b-4f0f8445c047
-- title:
--   Étale cohomology of a separably closed point vanishes: $H^{n+1}(\operatorname{Spec}\kappa, F) = 0$ for every étale sheaf $F$ when $\kappa$ is separably closed
-- statement:
--   Let $X$ be a scheme and $x_0 \in X$ a point such that the canonical morphism $\operatorname{Spec}\kappa(x_0) \to X$ is an isomorphism, so that $X$ is the spectrum of the field $\kappa = \kappa(x_0)$, and assume that $\kappa$ is separably closed. Let $\Lambda$ be a commutative ring and $\underline{\Lambda}$ the constant sheaf of $\Lambda$-modules on the small étale site of $X$. For an étale sheaf $F$ of $\Lambda$-modules on $X$ write
--
--   $$H^q(X, F) = \operatorname{Ext}^q(\underline{\Lambda}, F)$$
--
--   for its étale cohomology (Ext in the abelian category of étale sheaves of $\Lambda$-modules on $X$). Then for every étale sheaf $F$ of $\Lambda$-modules on $X$ and every $n \ge 0$,
--
--   $$H^{n+1}(X, F) = 0.$$
--
--   Over an arbitrary field $\kappa$, étale sheaves on $\operatorname{Spec}\kappa$ are the discrete modules over $\operatorname{Gal}(\kappa^{\mathrm{sep}}/\kappa)$ and étale cohomology of $\operatorname{Spec}\kappa$ is Galois cohomology. When $\kappa$ is separably closed the Galois group is trivial, the constant sheaf $\underline{\Lambda}$ is a projective object, and taking global sections is exact, so all higher cohomology vanishes. This is the dimension-zero case of the vanishing theorems of étale cohomology; it is what makes a closed point with separably (for instance algebraically) closed residue field cohomologically trivial, and it is used, for example, in excision computations at closed points of curves.
--
--   **Formalization Note**: The small étale site is `X.smallEtaleTopology`, and étale sheaves of $\Lambda$-modules are `Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)`. The hypothesis that $X$ is the spectrum of the field $\kappa(x_0)$ is `[IsIso (X.fromSpecResidueField x0)]`, and the hypothesis that $\kappa(x_0)$ is separably closed is `[IsSepClosed (X.residueField x0)]`. The constant sheaf $\underline{\Lambda}$ is `(constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj (ModuleCat.of Λ Λ)`, and $H^{n+1}(X, F)$ is `Abelian.Ext.{u}` from it to `F` in degree `n + 1`, with values in `Type u`, for the `HasExt` structure that Mathlib provides on this Grothendieck abelian category; its vanishing is stated as `Subsingleton`. All types live in one universe `u`. The statement is not vacuous: for every algebraically closed field $K$ (for example the algebraic closure of $\mathbb{Q}$), $X = \operatorname{Spec} K$ with its unique point $x_0$ satisfies both hypotheses.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter II, §1 (étale sheaves on the spectrum of a field and Galois modules) and Chapter III, §1 (étale cohomology of a field is Galois cohomology); A. Grothendieck, M. Artin, J.-L. Verdier, Théorie des topos et cohomologie étale des schémas (SGA 4), Exposé VIII

import Mathlib

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

theorem AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_succ_of_isSepClosed_point
    {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] [IsSepClosed (X.residueField x0)]
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (n : ℕ) :
    Subsingleton (Abelian.Ext.{u}
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj (ModuleCat.of Λ Λ)) F (n + 1)) := by
  sorry
