-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf
-- name    : AlgebraicCurve.exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/b55d5d5d-9f92-587f-b4db-e7393bd12108
-- title:
--   Regularity of generic germs at places centred in U
-- statement:
--   Let $k$ be a perfect field, $X$ an integral scheme and $c : X \to \operatorname{Spec} k$ a morphism that is smooth of relative dimension $1$; let $U \subseteq X$ be a nonempty open subscheme. The section ring $\Gamma(X,U)$ is regarded as a $k$-algebra through the composite of the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism with `c.appLE ⊤ U`, and the function field $X.\mathrm{functionField}$ is a $k$-algebra through `baseToFunctionField c`, the ring homomorphism obtained from $c$ on global sections followed by the germ map at the generic point of $X$. Let $\eta \in \Omega_{\Gamma(X,U)/k}$ be a Kähler differential, and let $v$ be a place of $X.\mathrm{functionField}$ over $k$ in the sense of the structure `Place`: a valuation subring $\mathcal{O}_v$ of the function field which contains the image of $k$, is not the whole field, and is a principal ideal ring. Assume $v$ lies in `placesOf c U`, i.e. there is a point $x \in U$ with $\{x\}$ closed in $X$ such that the image of the stalk $\mathcal{O}_{X,x}$ in the function field is exactly the subring underlying $\mathcal{O}_v$. Then there exists $f \in \mathcal{O}_v$ with $$\mathrm{kaehlerToFunctionField}\,c\,U\,(\eta) = f \cdot \mathrm{dCoord}(v),$$ where the left-hand side is the image of $\eta$ in $\Omega_{X.\mathrm{functionField}/k}$ under the map induced by the germ homomorphism $\Gamma(X,U) \to X.\mathrm{functionField}$, and $\mathrm{dCoord}(v) = d\pi_v$ for the chosen irreducible element $\pi_v$ of $\mathcal{O}_v$.
--
--   This is the local expression $\omega = f\,d\pi_v$ with $f$ regular at $v$, for the generic germ of a differential defined on $U$, at any place whose centre is a closed point of $U$. It is the per-place ingredient used to show that such generic germs lie in the module of regular differentials, and it feeds the vanishing of residues on Čech coboundaries for a two-chart affine cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_RegularDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [SmoothOfRelativeDimension 1 c]
    (U : X.Opens) [Nonempty U]
    (η : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U; Ω[Γ(X, U)⁄k])
    (v : letI := (baseToFunctionField c).toAlgebra; Place k X.functionField)
    (hv : letI := (baseToFunctionField c).toAlgebra; v ∈ placesOf c U) :
    letI := (baseToFunctionField c).toAlgebra
    ∃ f ∈ v.toValuationSubring, kaehlerToFunctionField c U η = f • v.dCoord := by sorry
