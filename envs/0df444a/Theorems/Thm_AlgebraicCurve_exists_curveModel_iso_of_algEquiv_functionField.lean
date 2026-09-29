-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_curveModel_iso_of_algEquiv_functionField
-- name    : AlgebraicCurve.exists_curveModel_iso_of_algEquiv_functionField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/2074cb16-911c-5b6d-bd26-5558d97bd50e
-- title:
--   Every field isomorphic to K(Y) has Y as a curve model
-- statement:
--   Let $k$ be an algebraically closed field, let $Y$ be a scheme and $\pi_Y : Y \to \operatorname{Spec} k$ a morphism with $Y$ integral and $\pi_Y$ proper and smooth of relative dimension $1$, and let $L$ be a field equipped with a $k$-algebra structure. Suppose given a ring isomorphism $\iota : L \xrightarrow{\sim} K(Y)$ onto the function field of $Y$ (the stalk of $\mathcal O_Y$ at the generic point) such that for every $a \in k$ one has $\iota(a \cdot 1) =$ the image of $a$ under `baseToFunctionField` $\pi_Y$, that is, under $k \cong \Gamma(\operatorname{Spec} k, \mathcal O) \to \Gamma(Y, \mathcal O_Y) \to K(Y)$. Then there exist a curve model $M$ of $L$ over $k$ — a scheme $M.C$ with a proper structure morphism $M.\mathrm{toBase} : M.C \to \operatorname{Spec} k$ that is smooth of relative dimension $1$, $M.C$ integral, a ring isomorphism $M.\mathrm{ffEquiv} : L \xrightarrow{\sim} K(M.C)$ carrying the $k$-algebra structure of $L$ to `baseToFunctionField` $M.\mathrm{toBase}$, a bijection from the closed points of $M.C$ to the set of places of $L/k$ (valuation subrings of $L$ containing the image of $k$, distinct from $L$ itself, and principal ideal rings) under which the image of the stalk at a closed point inside $L$ is exactly the corresponding valuation subring, and with every finite subset of $M.C$ contained in an affine open — together with an isomorphism of schemes $e : M.C \cong Y$ such that $e.\mathrm{hom}$ followed by $\pi_Y$ equals $M.\mathrm{toBase}$, and such that for every open $U \subseteq Y$ with $U$ and $e.\mathrm{hom}^{-1}U$ non-empty and every $t \in \Gamma(Y, U)$, the element of $L$ obtained by pulling $t$ back along $e.\mathrm{hom}$, taking its germ in $K(M.C)$ and applying $M.\mathrm{ffEquiv}^{-1}$ agrees with $\iota^{-1}$ of the germ of $t$ in $K(Y)$.
--
--   This is the transport, along an arbitrary $k$-isomorphism $L \cong K(Y)$, of the correspondence between smooth proper curves over an algebraically closed field and their function fields: any such $L$ admits $Y$ itself as a curve model, compatibly with germs of sections. It is used in the Čerednik–Drinfel'd part of the development, where a complex curve model of a quaternionic moduli curve is identified with a prescribed field of functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_curveModel_iso_of_algEquiv_functionField.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open AlgebraicCurve

theorem AlgebraicCurve.exists_curveModel_iso_of_algEquiv_functionField
    (k : Type) [Field k] [IsAlgClosed k] (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of k))
    [IsIntegral Y] [IsProper πY] [SmoothOfRelativeDimension 1 πY]
    (L : Type) [Field L] [Algebra k L]
    (ι : L ≃+* Y.functionField) (hι : ∀ a : k, ι (algebraMap k L a) = baseToFunctionField πY a) :
    ∃ (M : CurveModel k L) (e : M.C ≅ Y), e.hom ≫ πY = M.toBase ∧
      ∀ (U : Y.Opens) [Nonempty (Scheme.Opens.toScheme U)] [Nonempty (Scheme.Opens.toScheme (e.hom ⁻¹ᵁ U))]
        (t : Γ(Y, U)),
        M.ffEquiv.symm (M.C.germToFunctionField (e.hom ⁻¹ᵁ U) ((e.hom.app U).hom t)) = ι.symm (Y.germToFunctionField U t) := by sorry
