-- Prove2me | Theorems.Thm_DrinfeldCurve_slEquivariant_quadratic_of_isCuspidalOfType_of_perfectField
-- name    : DrinfeldCurve.slEquivariant_quadratic_of_isCuspidalOfType_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/e132ae98-d6b3-5ebf-8c31-2e83ce81b3bb
-- title:
--   Quadratic relation for SL₂-equivariant maps into the Drinfeld Tate module
-- statement:
--   Let $q$ and $\ell$ be primes, and let $k$ be a perfect field equipped with an algebra structure over $\mathbb{F}_{q^2}=$ `GaloisField q 2`, such that the coordinate ring `CoordRing q k` of the Drinfeld curve is a domain and its fraction field $F=$ `drinfeldFunctionField q k` is a curve over $k$ in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15) (principal divisors, every place with residue field finite over $k$, and $\Omega_{F/k}$ free of rank one over $F$). Assume `AbelJacobiCard` for the pair $(k,F)$ at $\ell$ with genus $g=q(q-1)/2$, i.e. for every $n$ the group of $\ell^n$-torsion points of $\mathrm{Pic}^0(F)$ has cardinality $\ell^{2gn}$. Let $E$ be a field containing $\mathbb{Q}_\ell$, let $\theta\colon \mathbb{F}_{q^2}^\times\to E^\times$ be a homomorphism, and let $\sigma$ be a representation of $\mathrm{GL}_2(\mathbb{Z}/q)$ on a finite-dimensional $E$-vector space $W$ which is cuspidal of type $\theta$ (dimension $q-1$, no nonzero vector fixed by all unipotents, trivial action of the scalars, and the prescribed identity between the characteristic polynomial of a torus element and that of the induced representation). Let $\rho$ be the representation of the subgroup $H=$ `hSubgroup q` of $\mathrm{GL}_2(\mathbb{Z}/q)\times\mathbb{F}_{q^2}^\times$ on $E\otimes_{\mathbb{Q}_\ell} V_\ell(\mathrm{Pic}^0 F)$ obtained from the action of $H$ on $F$ by $k$-algebra automorphisms, followed by the action on the rational Tate module $\mathbb{Q}_\ell\otimes_{\mathbb{Z}_\ell}T_\ell(\mathrm{Pic}^0 F)$ and base change to $E$. The assertion is that for every $E$-linear $u\colon W\to E\otimes_{\mathbb{Q}_\ell}V_\ell(\mathrm{Pic}^0 F)$ with $u\circ\sigma(g)=\rho(g,1)\circ u$ for all $g$ with $(g,1)\in H$, and for every $\alpha\in\mathbb{F}_{q^2}^\times$ and $g$ with $(g,\alpha)\in H$, the operator $A(v)=\rho(g,\alpha)\circ v\circ\sigma(g^{-1})$ on such linear maps satisfies $A(A(u))-(\theta(\alpha)+\theta(\alpha^q))\,A(u)+\theta(\alpha)\theta(\alpha^q)\,u=0$.
--
--   This is the step in the Drinfeld-curve realisation of the cuspidal representations of $\mathrm{GL}_2(\mathbb{F}_q)$ which shows that the extra symmetry $(g,\alpha)$ acts on the space of $\mathrm{SL}_2$-equivariant maps into the Tate module through a root of the quadratic polynomial with roots $\theta(\alpha)$ and $\theta(\alpha^q)$. It is used in the determination of the inertia labels attached to a newform whose associated representation contains a cuspidal type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DrinfeldCurve_slEquivariant_quadratic_of_isCuspidalOfType_of_perfectField.lean

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

theorem slEquivariant_quadratic_of_isCuspidalOfType_of_perfectField
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [PerfectField k]
    [IsDomain (CoordRing q k)] [AlgebraicCurve.IsCurveOver k (drinfeldFunctionField q k)]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hrank : AlgebraicCurve.AbelJacobiCard k (drinfeldFunctionField q k) ℓ (q * (q - 1) / 2))
    (E : Type*) [Field E] [Algebra ℚ_[ℓ] E] (θ : (GaloisField q 2)ˣ →* Eˣ)
    {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (σ : Representation E (CuspidalType.GL2 q) W) (hσ : CuspidalType.IsCuspidalOfType θ σ) :
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
    ∀ u : W →ₗ[E] (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))),
      (∀ (g : CuspidalType.GL2 q) (hg₁ : (g, (1 : (GaloisField q 2)ˣ)) ∈ hSubgroup q),
        u ∘ₗ σ g = ρ ⟨(g, 1), hg₁⟩ ∘ₗ u) →
      ∀ (α : (GaloisField q 2)ˣ) (g : CuspidalType.GL2 q) (hg : (g, α) ∈ hSubgroup q),
        let A : (W →ₗ[E] (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
              (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)))) →
            (W →ₗ[E] (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
              (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)))) :=
          fun v => ρ ⟨(g, α), hg⟩ ∘ₗ v ∘ₗ σ g⁻¹
        A (A u) - (((θ α : Eˣ) : E) + ((θ (α ^ q) : Eˣ) : E)) • A u +
          (((θ α : Eˣ) : E) * ((θ (α ^ q) : Eˣ) : E)) • u = 0 := by sorry
