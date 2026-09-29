-- Prove2me | Theorems.Thm_DrinfeldCurve_intertwiningMap_twist_eq_zero_of_isCuspidalOfType_of_perfectField
-- name    : DrinfeldCurve.intertwiningMap_twist_eq_zero_of_isCuspidalOfType_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/a9646fff-561e-5672-8a33-9ecca73f462e
-- title:
--   Vanishing of ψ-twisted intertwiners over a perfect base field
-- statement:
--   Fix a prime $q$ and a field $k$ that is perfect and carries an algebra structure over $\mathbf{F}_{q^2} =$ `GaloisField q 2`, and assume the Drinfeld coordinate ring `CoordRing q k` (the quotient of $k[x,y]$ by the Drinfeld ideal) is a domain and that its fraction field $F =$ `drinfeldFunctionField q k` is a curve over $k$ in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): principal divisors exist, each place has residue field finite over $k$, and $\Omega_{F/k}$ is free of rank one over $F$. Fix a prime $\ell$ and assume `AbelJacobiCard k F ℓ (q*(q-1)/2)`, i.e. for every $n$ the $\ell^n$-torsion of the degree-zero divisor class group $\mathrm{Pic}^0(F/k)$ has cardinality $\ell^{2\cdot(q(q-1)/2)\cdot n}$. Let $E$ be a field containing $\mathbf{Q}_\ell$, let $\theta,\psi : \mathbf{F}_{q^2}^{\times} \to E^{\times}$ be characters with $\psi \neq \theta$ and $\psi \neq \theta^{-1}$, and let $\sigma$ be a representation of $\mathrm{GL}_2(\mathbf{Z}/q)$ on a finite-dimensional $E$-vector space $W$ which is cuspidal of type $\theta$: $\dim_E W = q-1$, no nonzero vector is fixed by all unipotents `unipotent q t`, the scalars `scalarElem q c` act as the identity, and for every $\alpha \in \mathbf{F}_{q^2}^{\times}$ the characteristic polynomial of $\sigma(\text{torus } q\,\alpha)$ times $(X-\theta(\alpha))(X-\theta(\alpha)^{-1})$ equals that of the induced representation `ind q E` at the same torus element. Write $\rho$ for the representation of `hSubgroup q` (the kernel of `hChar q` in $\mathrm{GL}_2(\mathbf{Z}/q) \times \mathbf{F}_{q^2}^{\times}$) on $E \otimes_{\mathbf{Q}_\ell} (\mathbf{Q}_\ell \otimes_{\mathbf{Z}_\ell} T_\ell \mathrm{Pic}^0(F/k))$ obtained from the action `hFunctionFieldAction q k` of that subgroup by $k$-algebra automorphisms of $F$, via the rational Tate module representation and base change to $E$, and for a character $\chi$ write $\mathrm{twist}\,\chi$ for the representation of `hSubgroup q` on $W \otimes_E E$ given by $\sigma$ on the first factor tensored with $\chi$ acting by multiplication on the second, restricted along the inclusion of the subgroup. The assertion is that every intertwining map from $\mathrm{twist}\,\psi$ to $\rho$ is zero.
--
--   This is the statement that a cuspidal type $\theta$ of $\mathrm{GL}_2(\mathbf{F}_q)$ occurs in the $\ell$-adic Tate module of the Jacobian of the Drinfeld curve $xy^q - x^qy = 1$ only through the twists by $\theta$ and $\theta^{-1}$, here over a perfect base field containing $\mathbf{F}_{q^2}$ rather than an algebraically closed one, with the Abel–Jacobi torsion count of a $q(q-1)/2$-dimensional abelian variety taken as a hypothesis. It feeds the construction of the $\mathrm{SL}_2$-equivariant quadratic form attached to such a type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DrinfeldCurve_intertwiningMap_twist_eq_zero_of_isCuspidalOfType_of_perfectField.lean

import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Invariants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

namespace DrinfeldCurve

theorem intertwiningMap_twist_eq_zero_of_isCuspidalOfType_of_perfectField
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [PerfectField k]
    [IsDomain (CoordRing q k)] [AlgebraicCurve.IsCurveOver k (drinfeldFunctionField q k)]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hrank : AlgebraicCurve.AbelJacobiCard k (drinfeldFunctionField q k) ℓ (q * (q - 1) / 2))
    (E : Type*) [Field E] [Algebra ℚ_[ℓ] E] (θ : (GaloisField q 2)ˣ →* Eˣ)
    {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (σ : Representation E (CuspidalType.GL2 q) W) (hσ : CuspidalType.IsCuspidalOfType θ σ)
    (ψ : (GaloisField q 2)ˣ →* Eˣ) (hψ : ψ ≠ θ) (hψ' : ψ ≠ θ⁻¹) :
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
    let twist : ((GaloisField q 2)ˣ →* Eˣ) → Representation E (hSubgroup q) (W ⊗[E] E) := fun χ =>
      (Representation.tprod (σ.comp (MonoidHom.fst (CuspidalType.GL2 q) (GaloisField q 2)ˣ))
          ((Algebra.lmul E E).toMonoidHom.comp
            ((Units.coeHom E).comp (χ.comp (MonoidHom.snd (CuspidalType.GL2 q) (GaloisField q 2)ˣ))))).comp
        (hSubgroup q).subtype
    ∀ F : Representation.IntertwiningMap (twist ψ) ρ, F = 0 := by sorry
