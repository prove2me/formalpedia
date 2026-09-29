-- Prove2me | Theorems.Thm_DrinfeldCurve_finrank_eigenspace_rootsOfUnity_rationalTateModule_eq
-- name    : DrinfeldCurve.finrank_eigenspace_rootsOfUnity_rationalTateModule_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/0c6543d0-583b-5a65-b7e5-348cb7c655a4
-- title:
--   Dimensions of μ_{q+1}-eigenspaces on the Drinfeld curve
-- statement:
--   Let $q$ be a prime and let $k$ be a field which is algebraically closed and an algebra over $\mathrm{GaloisField}\,q\,2 = \mathbb{F}_{q^2}$, such that the coordinate ring `CoordRing q k`, the quotient of $k[X_0,X_1]$ by the Drinfeld ideal, is a domain; write $F =$ `drinfeldFunctionField q k` for its fraction field, and assume [`AlgebraicCurve.IsCurveOver k F`](def/AlgebraicCurve_IsCurveOver.html#L15), i.e. every nonzero element of $F$ has a degree-zero divisor recording its orders at all places, every place of $F/k$ has residue field finite over $k$, and $\Omega[F/k]$ is free of rank one over $F$. Let $\ell$ be a prime with $\ell \neq q$, and assume `AbelJacobiCard`: for every $n$, the $\ell^n$-torsion of $\mathrm{Pic}^0 =$ (degree-zero divisors)/(principal divisors) has cardinality $\ell^{2gn}$ with $g = q(q-1)/2$ (natural-number division). Let $E$ be a field with a $\mathbb{Q}_\ell$-algebra structure. Let $\rho$ be the representation of `hSubgroup q` (the kernel of `hChar q` inside $\mathrm{GL}_2(\mathbb{Z}/q) \times \mathbb{F}_{q^2}^{\times}$) on $E \otimes_{\mathbb{Q}_\ell} (\mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} T_\ell \mathrm{Pic}^0)$ obtained from `hFunctionFieldAction q k`, the resulting action on the rational Tate module, and base change of endomorphisms to $E$. Then for every homomorphism $\theta$ from the group of $(q+1)$-st roots of unity in $\mathbb{F}_{q^2}$ to $E^{\times}$, the $E$-dimension of $\bigcap_{\zeta} \ker(\rho(1,\zeta) - \theta(\zeta))$ equals $q-1$ if $\theta \neq 1$, and $0$ if $\theta = 1$.
--
--   This is the numerical half of the Deligne–Lusztig description of the cohomology of the Drinfeld curve for $\mathrm{SL}_2(\mathbb{F}_q)$: the $\theta$-eigenspace for the central torus $\mu_{q+1}$ has dimension $q-1$ for $\theta$ nontrivial and vanishes for $\theta$ trivial. It feeds the construction of cuspidal representations of type $\theta$, being used in [`DrinfeldCurve.intertwiningMap_twist_eq_zero_of_isCuspidalOfType_of_isAlgClosed`](thm.html#DrinfeldCurve.intertwiningMap_twist_eq_zero_of_isCuspidalOfType_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DrinfeldCurve_finrank_eigenspace_rootsOfUnity_rationalTateModule_eq.lean

import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_JZeroTateModule
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

namespace DrinfeldCurve

theorem finrank_eigenspace_rootsOfUnity_rationalTateModule_eq
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
    [IsDomain (CoordRing q k)] [AlgebraicCurve.IsCurveOver k (drinfeldFunctionField q k)]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ q)
    (hrank : AlgebraicCurve.AbelJacobiCard k (drinfeldFunctionField q k) ℓ (q * (q - 1) / 2))
    (E : Type*) [Field E] [Algebra ℚ_[ℓ] E] :
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
    ∀ θ : rootsOfUnity (q + 1) (GaloisField q 2) →* Eˣ,
      (θ ≠ 1 →
        Module.finrank E
            ↥(⨅ (ζ : rootsOfUnity (q + 1) (GaloisField q 2)),
                LinearMap.ker (ρ ⟨_, one_mem_hSubgroup_of_mem q ζ⟩ - ((θ ζ : Eˣ) : E) • 1)) = q - 1) ∧
      (θ = 1 →
        Module.finrank E
            ↥(⨅ (ζ : rootsOfUnity (q + 1) (GaloisField q 2)),
                LinearMap.ker (ρ ⟨_, one_mem_hSubgroup_of_mem q ζ⟩ - ((θ ζ : Eˣ) : E) • 1)) = 0) := by sorry
