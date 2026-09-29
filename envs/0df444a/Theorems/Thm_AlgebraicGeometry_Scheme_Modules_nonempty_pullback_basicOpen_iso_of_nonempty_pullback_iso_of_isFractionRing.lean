-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_basicOpen_iso_of_nonempty_pullback_iso_of_isFractionRing
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_pullback_basicOpen_iso_of_nonempty_pullback_iso_of_isFractionRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/cd99ff2b-4e8e-58a5-bdb0-0a48a10d1a13
-- title:
--   Generic fibre over a DVR is the basic open of varpi
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain, let $\varpi \in R$ satisfy $\mathrm{maximalIdeal}(R) = (\varpi)$, and let $KK$ be a field with an $R$-algebra structure making it a fraction field of $R$. Let $f : X \to \operatorname{Spec} R$ be a morphism of schemes (in universe $0$), and let $gK : XK \to X$, $fK : XK \to \operatorname{Spec} KK$ form a pullback square with $f$ and with $\operatorname{Spec}$ of the structure map $R \to KK$, the square being cartesian in the sense that $gK, fK$ is a pullback cone over $f$ and $\operatorname{Spec}(R \to KK)$. Let $M, M'$ be objects of $X.\mathrm{Modules}$, and assume the type of isomorphisms between their pullbacks along $gK$ is nonempty. Write $t := f^{\#}(\varpi) \in \Gamma(X,\mathcal O_X)$ for the image of $\varpi$ under the global-sections map of $f$ composed with the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism for $R$. The conclusion is the conjunction of two assertions: first, a point $x \in X$ lies in the basic open $X_t$ if and only if $f(x)$ is not the closed point of $\operatorname{Spec} R$; second, the type of isomorphisms between the pullbacks of $M$ and of $M'$ along the open immersion $X_t \hookrightarrow X$ is nonempty.
--
--   This identifies the generic fibre of a scheme over a discrete valuation ring with the basic open set of a uniformiser, and transports an isomorphism of $\mathcal O$-modules from the generic fibre to that open set. It is used in the proof that an isomorphism of invertible modules over a scheme over a discrete valuation ring, given on the generic fibre, already exists over the whole scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_basicOpen_iso_of_nonempty_pullback_iso_of_isFractionRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_basicOpen_iso_of_nonempty_pullback_iso_of_isFractionRing
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (KK : Type) [Field KK] [Algebra R KK] [IsFractionRing R KK]
    {X XK : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (fK : XK ⟶ Spec (CommRingCat.of KK)) (gK : XK ⟶ X) (hgK : IsPullback gK fK f (Spec.map (CommRingCat.ofHom (algebraMap R KK))))
    (M M' : X.Modules) (h : Nonempty ((Scheme.Modules.pullback gK).obj M ≅ (Scheme.Modules.pullback gK).obj M')) :
    (∀ x : X, x ∈ X.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ)) ↔ f.base x ≠ IsLocalRing.closedPoint R) ∧
      Nonempty ((Scheme.Modules.pullback (X.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ))).ι).obj M ≅
        (Scheme.Modules.pullback (X.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ))).ι).obj M') := by sorry
