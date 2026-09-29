-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_section_closedFibre_fromNormalization_kummer_of_henselianLocalRing
-- name    : AlgebraicGeometry.exists_section_closedFibre_fromNormalization_kummer_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/1cb0ac7e-7609-5508-8641-89801c2c8572
-- title:
--   Kummer cover of a proper scheme splits over the closed fibre
-- statement:
--   Let $R$ be a noetherian henselian local ring whose residue field is algebraically closed, let $X$ be an integral scheme and let $f : X \to \operatorname{Spec} R$ be a proper morphism; assume every local ring $\mathcal O_{X,x}$ is integrally closed in its fraction field. Let $k$ be a natural number whose image in $R$ is a unit, and let $g$ be a nonzero element of the function field $K(X)$. Assume given finitely many open subsets $U_0,\dots,U_{r-1}$ of $X$ covering $X$ and nonzero $h_a \in K(X)$ such that for each $a$ and each point $x \in U_a$ both $g/h_a^k$ and $h_a^k/g$ lie in the image of $\mathcal O_{X,x} \to K(X)$, and such that for all $a,b$ and all $x \in U_a \cap U_b$ there are $t$ in the maximal ideal of $R$ and $s$ in the image of $\mathcal O_{X,x} \to K(X)$ with $h_a = h_b\,(1 + \iota(t)\,s)$, where $\iota : R \to K(X)$ is the composite of $R \cong \Gamma(\operatorname{Spec} R,\mathcal O)$, the map $f$ on global sections, and the germ at the generic point. Assume finally that the global-sections map of the second projection $X \times_{\operatorname{Spec} R} \operatorname{Spec} \kappa \to \operatorname{Spec} \kappa$, $\kappa$ the residue field of $R$, is bijective. Write $\pi$ for the morphism from the normalisation of $X$ in the composite $\operatorname{Spec}\bigl(K(X)[T]/(T^k-g)\bigr) \to \operatorname{Spec} K(X) \to X$, the second map being `X.fromSpecStalk` at the generic point. Then there is a morphism $s_0$ from $X \times_{\operatorname{Spec} R} \operatorname{Spec}\kappa$ to that normalisation such that $s_0$ followed by $\pi$ is the first projection $X \times_{\operatorname{Spec} R} \operatorname{Spec}\kappa \to X$.
--
--   This is the splitting step for a Kummer covering $T^k = g$ of a proper scheme over a henselian local ring: the hypotheses say that $\operatorname{div}(g)$ is $k$ times the Cartier divisor given by the local equations $h_a$ and that the transition cocycle of the associated line bundle is congruent to $1$ modulo the maximal ideal of $R$, and the conclusion produces a section of the cover over the closed fibre. It is used in the combined statement that this Kummer cover is finite and étale and splits over the closed fibre, and its construction rests on the unique-lifting property of roots recorded in [`AlgebraicGeometry.exists_root_fromNormalization_kummer_existsUnique_lift`](thm.html#AlgebraicGeometry.exists_root_fromNormalization_kummer_existsUnique_lift).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_section_closedFibre_fromNormalization_kummer_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

theorem AlgebraicGeometry.exists_section_closedFibre_fromNormalization_kummer_of_henselianLocalRing
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
    ∃ s₀ : pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ⟶ (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
        X.fromSpecStalk (genericPoint X)).normalization,
      s₀ ≫ π = pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) := by sorry
