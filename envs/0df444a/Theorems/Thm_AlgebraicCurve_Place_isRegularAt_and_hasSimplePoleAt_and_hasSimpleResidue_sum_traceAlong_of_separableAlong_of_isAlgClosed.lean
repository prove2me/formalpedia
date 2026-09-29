-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_sum_traceAlong_of_separableAlong_of_isAlgClosed
-- name    : AlgebraicCurve.Place.isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_sum_traceAlong_of_separableAlong_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/e35bcff4-b8ae-5bc2-9cdd-0823b443224e
-- title:
--   Trace of differentials preserves regularity, simple poles and residues
-- statement:
--   Let $K$ be an algebraically closed field and $F$, $F'$ two field extensions of $K$ each of one-variable function field type in the following sense: there is $x \in F$ transcendental over $K$ with $F$ finite-dimensional over the intermediate field $K(x)$, and likewise $x' \in F'$ with $F'$ finite-dimensional over $K(x')$; moreover $F'$ satisfies `HasPrincipalDivisors`, i.e. every nonzero $f \in F'$ has a divisor $D$ with $D(w) = \operatorname{ord}_w f$ at every place $w$ and $\deg D = 0$. Let $\varphi \colon F \to F'$ be a $K$-algebra map whose underlying ring map is integral, and assume `SeparableAlong`, i.e. $F'$ is a separable algebra over $F$ via $\varphi$. Let $v$ be a place of $F$ (a valuation subring of $F$ containing the image of $K$, not equal to $F$, and a principal ideal ring) and let $\eta \in \Omega_{F'/K}$. Here $\mathrm{traceAlong}\ \varphi$ is the $K$-linear map $\Omega_{F'/K} \to \Omega_{F/K}$ obtained, using separability (hence formal étaleness) to identify $\Omega_{F'/K}$ with $F' \otimes_F \Omega_{F/K}$, by applying $\operatorname{Tr}_{F'/F}$ to the first tensor factor; the fibre $\mathrm{fiberAlong}\ \varphi$ of $v$ is the finite set of places $w$ of $F'$ lying over $v$. Three assertions are made, each with the same local vocabulary: $\omega$ is regular at a place if $\omega = f \cdot d\pi$ with $f$ in the valuation subring and $\pi$ the chosen uniformiser; $\omega$ has a simple pole if $\omega = f \cdot d\pi$ with $\pi f$ in the valuation subring; and $\omega$ has simple residue $a \in K$ if $\omega = f \cdot d\pi$ and $\pi f$ lies in the valuation subring with residue the image of $a$. Then: (i) if $\eta$ is regular at every $w$ in the fibre of $v$, then $\mathrm{traceAlong}\ \varphi\ \eta$ is regular at $v$; (ii) if $\eta$ has a simple pole at every such $w$, then $\mathrm{traceAlong}\ \varphi\ \eta$ has a simple pole at $v$; and (iii) for every function $r$ from places of $F'$ to $K$, if $\eta$ has simple residue $r(w)$ at each $w$ in the fibre, then $\mathrm{traceAlong}\ \varphi\ \eta$ has simple residue $\sum_{w \mid v} r(w)$ at $v$.
--
--   This is the compatibility of the trace map on differentials with residues for a separable integral morphism of one-variable function fields, in the form valid over an algebraically closed base, where all residue fields are $K$ and the fibre sum carries no residue-degree weights. It is used in the analysis of Hecke correspondences acting on differentials, where the residue of a trace at a place of the target is computed as the sum of residues over the places above it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_sum_traceAlong_of_separableAlong_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_PolarDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_sum_traceAlong_of_separableAlong_of_isAlgClosed
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [IsAlgClosed K]
    {x : F} (htr : Transcendental K x) (hfd : FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F)
    {x' : F'} (htr' : Transcendental K x') (hfd' : FiniteDimensional ↥(IntermediateField.adjoin K ({x'} : Set F')) F')
    [AlgebraicCurve.HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hsep : AlgebraicCurve.SeparableAlong K φ)
    (v : AlgebraicCurve.Place K F) (η : Ω[F'⁄K]) :
    ((∀ w ∈ AlgebraicCurve.Place.fiberAlong φ hφ v, w.IsRegularAt η) →
        v.IsRegularAt (AlgebraicCurve.Differential.traceAlong φ η)) ∧
    ((∀ w ∈ AlgebraicCurve.Place.fiberAlong φ hφ v, w.HasSimplePoleAt η) →
        v.HasSimplePoleAt (AlgebraicCurve.Differential.traceAlong φ η)) ∧
    (∀ r : AlgebraicCurve.Place K F' → K,
      (∀ w ∈ AlgebraicCurve.Place.fiberAlong φ hφ v, w.HasSimpleResidue η (r w)) →
        v.HasSimpleResidue (AlgebraicCurve.Differential.traceAlong φ η)
          (∑ w ∈ AlgebraicCurve.Place.fiberAlong φ hφ v, r w)) := by sorry
