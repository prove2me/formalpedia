-- Prove2me | Theorems.Thm_DrinfeldCurve_intertwiningMap_twist_eq_zero_of_isCuspidalOfType_of_isAlgClosed
-- name    : DrinfeldCurve.intertwiningMap_twist_eq_zero_of_isCuspidalOfType_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/fa2be08a-6585-509f-8929-a1dfe952c0fb
-- title:
--   Twists by characters other than θ^{± 1} do not occur
-- statement:
--   Let $q$ be a prime and let $k$ be an algebraically closed field equipped with an algebra structure over the field $\mathbb{F}_{q^2}$ (`GaloisField q 2`), such that the coordinate ring `CoordRing q k` of the Drinfeld curve (a quotient of $k[X_0,X_1]$ by the Drinfeld ideal) is a domain and such that its fraction field $F =$ `drinfeldFunctionField q k` is a curve over $k$ in the sense that divisors of functions are the principal divisors, each place of $F/k$ has residue field finite over $k$, and $\Omega_{F/k}$ is free of rank one over $F$. Let $\ell \neq q$ be a prime, and assume the Abel–Jacobi count $\#\,\mathrm{Pic}^0(F/k)[\ell^n] = \ell^{2gn}$ for all $n$, with $g = q(q-1)/2$. Let $E$ be a field that is a $\mathbb{Q}_\ell$-algebra, $\theta : \mathbb{F}_{q^2}^\times \to E^\times$ a character, $W$ a finite-dimensional $E$-vector space and $\sigma$ a representation of $\mathrm{GL}_2(\mathbb{Z}/q)$ on $W$ which is cuspidal of type $\theta$: $\dim_E W = q-1$, no nonzero vector is fixed by all unipotents `unipotent q t`, the scalars `scalarElem q c` act as the identity, and for every $\alpha \in \mathbb{F}_{q^2}^\times$ the characteristic polynomial of $\sigma(\mathrm{torus}(\alpha))$ times $(X - \theta(\alpha))(X - \theta(\alpha)^{-1})$ equals that of $\mathrm{torus}(\alpha)$ in the induced representation `ind q E`. Let $\psi : \mathbb{F}_{q^2}^\times \to E^\times$ be a character with $\psi \neq \theta$ and $\psi \neq \theta^{-1}$. Write $\rho$ for the representation of `hSubgroup q`, the kernel of `hChar q` inside $\mathrm{GL}_2(\mathbb{Z}/q) \times \mathbb{F}_{q^2}^\times$, on $E \otimes_{\mathbb{Q}_\ell} V_\ell(\mathrm{Pic}^0(F/k))$ obtained from the action of `hSubgroup q` by $k$-algebra automorphisms of $F$ via `hFunctionFieldAction`, the induced rational Tate module representation, and base change of endomorphisms to $E$; and write $\mathrm{twist}(\psi)$ for the representation of `hSubgroup q` on $W \otimes_E E$ in which the first factor acts through $\sigma$ and the second through multiplication by $\psi$, restricted along the inclusion of `hSubgroup q`. Then every intertwining map $F$ from $\mathrm{twist}(\psi)$ to $\rho$ is zero.
--
--   This is the multiplicity-zero half of the Drinfeld-curve realisation of the cuspidal representations of $\mathrm{GL}_2(\mathbb{F}_q)$: in the $\ell$-adic Tate module of the Jacobian of the Drinfeld curve, the twist of a cuspidal representation of type $\theta$ by a character $\psi$ occurs only for $\psi = \theta^{\pm 1}$. It is the algebraically closed base case from which the version over a perfect constant field, [`DrinfeldCurve.intertwiningMap_twist_eq_zero_of_isCuspidalOfType_of_perfectField`](thm.html#DrinfeldCurve.intertwiningMap_twist_eq_zero_of_isCuspidalOfType_of_perfectField), is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DrinfeldCurve_intertwiningMap_twist_eq_zero_of_isCuspidalOfType_of_isAlgClosed.lean

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

theorem intertwiningMap_twist_eq_zero_of_isCuspidalOfType_of_isAlgClosed
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
    [IsDomain (CoordRing q k)] [AlgebraicCurve.IsCurveOver k (drinfeldFunctionField q k)]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ q)
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
