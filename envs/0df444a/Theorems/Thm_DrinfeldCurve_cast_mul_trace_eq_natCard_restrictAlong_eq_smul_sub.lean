-- Prove2me | Theorems.Thm_DrinfeldCurve_cast_mul_trace_eq_natCard_restrictAlong_eq_smul_sub
-- name    : DrinfeldCurve.cast_mul_trace_eq_natCard_restrictAlong_eq_smul_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/b8d33a5d-791d-56fb-a690-91a541c19af8
-- title:
--   Character of H on the Drinfeld curve's Tate module
-- statement:
--   Fix a prime $q$ and a field $k$ of characteristic-$q$ type which is an algebra over $\mathbb{F}_{q^2}=$ `GaloisField q 2` and is algebraically closed, such that the coordinate ring `CoordRing q k` of the Drinfeld curve is a domain and its fraction field $F=$ `drinfeldFunctionField q k` satisfies [`AlgebraicCurve.IsCurveOver k`](def/AlgebraicCurve_IsCurveOver.html#L15), i.e. principal divisors, residue fields at all places finite over $k$, and $\Omega_{F/k}$ free of rank $1$. Fix a prime $\ell\neq q$ such that `AbelJacobiCard` holds with genus $g=q(q-1)/2$: $\#\mathrm{Pic}^0(F)[\ell^n]=\ell^{2gn}$ for all $n$. Let $E$ be a field that is a $\mathbb{Q}_\ell$-algebra, let $\varphi:F\to F$ be a $k$-algebra endomorphism whose underlying ring map is integral and which sends the classes of $x$ and $y$ to their $q^2$-th powers, and let $\zeta$ be a $(q+1)$-st root of unity in $\mathbb{F}_{q^2}$ with value $-1$. Write $\rho$ for the representation of the group `hSubgroup q` (the kernel of `hChar q` inside $\mathrm{GL}_2(\mathbb{Z}/q)\times\mathbb{F}_{q^2}^\times$) on $E\otimes_{\mathbb{Q}_\ell}\bigl(\mathbb{Q}_\ell\otimes_{\mathbb{Z}_\ell}T_\ell\mathrm{Pic}^0(F)\bigr)$ obtained from the action `hFunctionFieldAction q k` on $F$ by $k$-algebra automorphisms, followed by the induced action on the rational Tate module and base change of endomorphisms to $E$. Then for every $h\in$ `hSubgroup q`, $q\cdot\operatorname{tr}_E\rho(h)$ equals the cardinality, viewed in $E$, of the set of places $w$ of $F/k$ with $\varphi$-restriction `Place.restrictAlong φ hφi w` equal to the translate of $w$ by the automorphism attached to $(1,\zeta)\,h^{-1}$, minus $q^2+1$.
--
--   This is the character of the group $H$ acting on the $\ell$-adic Tate module of the Jacobian of the Drinfeld (Deligne–Lusztig) curve for $\mathrm{SL}_2$, expressed through the twisted fixed-point counts $\#\{w : \mathrm{Fr}(w)=hw\}$ obtained from the Lefschetz trace formula for a twisted $q^2$-Frobenius. It is used to compute the dimensions of the eigenspaces of the $(q+1)$-st roots of unity on the rational Tate module and to show the vanishing of the relevant twisted intertwining maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DrinfeldCurve_cast_mul_trace_eq_natCard_restrictAlong_eq_smul_sub.lean

import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_Correspondence
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

namespace DrinfeldCurve

theorem cast_mul_trace_eq_natCard_restrictAlong_eq_smul_sub
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
    [IsDomain (CoordRing q k)] [AlgebraicCurve.IsCurveOver k (drinfeldFunctionField q k)]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ q)
    (hrank : AlgebraicCurve.AbelJacobiCard k (drinfeldFunctionField q k) ℓ (q * (q - 1) / 2))
    (E : Type*) [Field E] [Algebra ℚ_[ℓ] E]
    (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) (hφi : φ.toRingHom.IsIntegral)
    (hφx : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) ^ q ^ 2)
    (hφy : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) ^ q ^ 2)
    (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) (hζ : ((ζ : (GaloisField q 2)ˣ) : GaloisField q 2) = -1) :
    let ρ : Representation E (hSubgroup q)
        (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) :=
      (Module.End.baseChangeHom ℚ_[ℓ] E
          (ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) :
        Module.End ℚ_[ℓ]
            (ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) →*
          Module.End E (E ⊗[ℚ_[ℓ]]
            ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)))).comp
        ((ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))
            (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k)).comp (hFunctionFieldAction q k))
    ∀ h : hSubgroup q,
      (q : E) * LinearMap.trace E _ (ρ h) =
        (Nat.card {w : AlgebraicCurve.Place k (drinfeldFunctionField q k) //
            AlgebraicCurve.Place.restrictAlong φ hφi w =
              hFunctionFieldAction q k (⟨_, one_mem_hSubgroup_of_mem q ζ⟩ * h⁻¹) • w} : E)
          - ((q : E) ^ 2 + 1) := by sorry
