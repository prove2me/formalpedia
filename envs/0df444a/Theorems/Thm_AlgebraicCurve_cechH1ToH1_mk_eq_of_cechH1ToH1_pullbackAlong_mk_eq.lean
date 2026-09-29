-- Prove2me | Theorems.Thm_AlgebraicCurve_cechH1ToH1_mk_eq_of_cechH1ToH1_pullbackAlong_mk_eq
-- name    : AlgebraicCurve.cechH1ToH1_mk_eq_of_cechH1ToH1_pullbackAlong_mk_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/fd8c2061-67b0-5584-a516-d4c18b7464c7
-- title:
--   Reflection of H¹(0)-class equality along an isomorphism
-- statement:
--   Let $K$ be a field and let $F$, $F_1$ be fields equipped with $K$-algebra structures. Let $\theta \colon F \to F_1$ be a $K$-algebra homomorphism which is integral as a ring homomorphism and bijective. Let $S_0, S_1$ be sets of places of $F$ over $K$ (valuation subrings of $F$ containing the image of $K$, proper, and principal ideal rings) whose union is the set of all such places, and let $a, b$ be elements of $L_{S_0 \cap S_1}(0)$, the $K$-subspace of $f \in F$ with $v(f) \le 1$ for every $v \in S_0 \cap S_1$. Write $[\,\cdot\,]$ for the class in the Čech group $\mathrm{cechH1}\,S_0\,S_1\,0$, the quotient of $L_{S_0 \cap S_1}(0)$ by the range of the Čech differential on $L_{S_0}(0) \times L_{S_1}(0)$, and let $\mathrm{cechH1ToH1}$ be the induced map to $H^1(0)$, the quotient of the ring of répartitions by the sum of the répartitions bounded by the divisor $0$ and the principal répartitions, obtained from extension off the chart $S_0$. Assume that the images of $[a]$ and $[b]$ under the pullback map $\mathrm{cechH1.pullbackAlong}\ \theta$ — composition with $\theta$, landing in the Čech group for the preimages of $S_0$ and $S_1$ under restriction of places along $\theta$, which cover all places of $F_1$ by `preimage_restrictAlong_union_eq_univ` — have the same image in $H^1(0 : \mathrm{Divisor}\,K\,F_1)$. Then $\mathrm{cechH1ToH1}$ sends $[a]$ and $[b]$ to the same element of $H^1(0 : \mathrm{Divisor}\,K\,F)$.
--
--   This is the functoriality of the Čech-to-répartition comparison map for the zero divisor under an isomorphism of function fields, in the minimal form in which no induced map on $H^1$ is constructed: equality of classes is merely reflected. It is used in the treatment of correspondences, in [`AlgebraicCurve.cechH1ToH1_corrH1_of_pullback_specMap_self`](thm.html#AlgebraicCurve.cechH1ToH1_corrH1_of_pullback_specMap_self).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_cechH1ToH1_mk_eq_of_cechH1ToH1_pullbackAlong_mk_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_CechH1PushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.cechH1ToH1_mk_eq_of_cechH1ToH1_pullbackAlong_mk_eq
    {K : Type*} {F F₁ : Type*} [Field K] [Field F] [Algebra K F] [Field F₁] [Algebra K F₁]
    (θ : F →ₐ[K] F₁) (hθ : θ.toRingHom.IsIntegral) (hbij : Function.Bijective θ)
    {S₀ S₁ : Set (Place K F)} (hS : S₀ ∪ S₁ = Set.univ)
    (a b : ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F)))
    (h : cechH1ToH1 (preimage_restrictAlong_union_eq_univ θ hθ hS) 0
        (cechH1.pullbackAlong θ hθ S₀ S₁ (Submodule.Quotient.mk a)) =
      cechH1ToH1 (preimage_restrictAlong_union_eq_univ θ hθ hS) 0
        (cechH1.pullbackAlong θ hθ S₀ S₁ (Submodule.Quotient.mk b))) :
    cechH1ToH1 hS 0 (Submodule.Quotient.mk a) = cechH1ToH1 hS 0 (Submodule.Quotient.mk b) := by sorry
