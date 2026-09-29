-- Prove2me | Theorems.Thm_AlgebraicGeometry_isFinite_and_etale_and_exists_section_fromNormalization_kummer_of_henselianLocalRing
-- name    : AlgebraicGeometry.isFinite_and_etale_and_exists_section_fromNormalization_kummer_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/f2e4d3d1-7b7f-535a-874f-d3b4cbb24e8c
-- title:
--   Kummer cover of a normal proper scheme: finite étale with section over the closed fibre
-- statement:
--   Let $R$ be a noetherian henselian local ring whose residue field $\mathrm{ResidueField}\,R$ is algebraically closed, let $X$ be an integral scheme and $f \colon X \to \operatorname{Spec} R$ a proper morphism, and assume every local ring $\mathcal{O}_{X,x}$ is integrally closed in its fraction field. Let $k$ be a natural number whose image in $R$ is a unit, and let $g \neq 0$ in the function field $K(X)$ of $X$. Assume given finitely many open subsets $U_0,\dots,U_{r-1}$ of $X$ with $\bigcup_a U_a = X$ and nonzero elements $h_a \in K(X)$ such that for every $a$ and every point $x \in U_a$ both $g/h_a^k$ and $h_a^k/g$ lie in the image of $\mathcal{O}_{X,x} \to K(X)$, and such that for all $a,b$ and all $x \in U_a \cap U_b$ there are $t$ in the maximal ideal of $R$ and $s$ in the image of $\mathcal{O}_{X,x} \to K(X)$ with $h_a = h_b(1 + \bar t\, s)$, where $\bar t$ denotes the image of $t$ in $K(X)$ under $R \to \Gamma(X,\mathcal{O}_X) \to K(X)$ (global sections along $f$, followed by the germ at the generic point). Assume finally that the map on global sections induced by the second projection of the fibre product of $f$ with $\operatorname{Spec}$ of the residue map $R \to \mathrm{ResidueField}\,R$ is bijective. Let $\pi$ be the morphism obtained from the composite of $\operatorname{Spec}$ of the structure map $K(X) \to K(X)[T]/(T^k - g)$ with $X.\mathrm{fromSpecStalk}$ at the generic point, by passing to the relative normalisation (`fromNormalization`). Then $\pi$ is finite and étale, and there is a morphism $s_0$ from the fibre product of $f$ with $\operatorname{Spec}$ of the residue map to the normalisation scheme such that $s_0$ followed by $\pi$ equals the first projection of that fibre product.
--
--   This is the geometric input for the Kummer-covering argument on a semistable model: the degree-$k$ cover of $X$ cut out by $T^k = g$, normalised, is finite étale when $k$ is invertible and the local rings of $X$ are normal, and the cocycle condition $h_a \equiv h_b$ modulo $\mathfrak{m}_R$ together with $\Gamma$ of the closed fibre being the residue field forces the cover to be split over the closed fibre. It is used in the divisor-class-group computations for semistable models, in the statements about when a multiple of a divisor class being principal forces the class itself to be principal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isFinite_and_etale_and_exists_section_fromNormalization_kummer_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

theorem AlgebraicGeometry.isFinite_and_etale_and_exists_section_fromNormalization_kummer_of_henselianLocalRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (k : ℕ) (hk : IsUnit ((k : ℕ) : R))
    (g : X.functionField) (hg : g ≠ 0)
    (r : ℕ) (U : Fin r → X.Opens) (hU : (⨆ a, U a) = ⊤) (h : Fin r → X.functionField) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (x : X), x ∈ U a →
      g / h a ^ k ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range ∧
      h a ^ k / g ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range)
    (hcoc : ∀ a b (x : X), x ∈ U a → x ∈ U b →
      ∃ t ∈ IsLocalRing.maximalIdeal R, ∃ s ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range,
        h a = h b * (1 + AlgebraicCurve.SemistableModel.baseToFunctionField f t * s))
    (hconn : Function.Bijective
      (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).appTop) :
    let π := (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X)).fromNormalization
    IsFinite π ∧ AlgebraicGeometry.Etale π ∧
      ∃ s₀ : pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ⟶ (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
          X.fromSpecStalk (genericPoint X)).normalization,
        s₀ ≫ π = pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) := by sorry
