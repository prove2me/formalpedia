-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_injective_linearMap_rationalTateModule_fixedField_range_eq_iInf_ker_and_comp_eq
-- name    : AlgebraicCurve.Pic0.exists_injective_linearMap_rationalTateModule_fixedField_range_eq_iInf_ker_and_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/6c01802d-ec19-5fbb-9bf5-af24e5df5729
-- title:
--   Rational Tate module of Pic⁰ of a quotient curve
-- statement:
--   Let $k$ be an algebraically closed field and $F$ a field extension of $k$ which is a curve over $k$ in the project's sense: every nonzero $f \in F$ has a divisor (a finitely supported $\mathbb{Z}$-valued function on the places of $F/k$, a place being a proper valuation subring of $F$ containing $k$ and a principal ideal ring) whose value at each place $v$ is $\mathrm{ord}_v(f)$ and whose degree is $0$, each place has residue field finite over $k$, and $\Omega_{F/k}$ is free of rank one over $F$. Let $G$ be a finite subgroup of the group of $k$-automorphisms of $F$, and assume the fixed field $F^G$ is likewise a curve over $k$; let $\ell$ be a prime. Writing $\mathrm{Pic}^0$ for degree-zero divisors modulo principal divisors, $T_\ell$ for the group of sequences $(x_n)$ with $\ell^n x_n = 0$ and $\ell x_{n+1} = x_n$, and $V = \mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} T_\ell$, the assertion is that there is a $\mathbb{Q}_\ell$-linear map $\Phi : V(\mathrm{Pic}^0(F^G/k)) \to V(\mathrm{Pic}^0(F/k))$ which is injective, whose range is $\bigcap_{g \in G} \ker(\rho(g) - 1)$ for the representation $\rho$ of $\mathrm{Aut}_k(F)$ on $V(\mathrm{Pic}^0(F/k))$ obtained by base change from the componentwise action on the Tate module, and which satisfies $\Phi \circ \rho_0(\tau) = \rho(\sigma) \circ \Phi$ whenever $\sigma \in \mathrm{Aut}_k(F)$ and $\tau \in \mathrm{Aut}_k(F^G)$ agree on $F^G$, where $\rho_0$ is the corresponding representation on $V(\mathrm{Pic}^0(F^G/k))$.
--
--   This is the statement that pull-back of degree-zero divisor classes along $F^G \subseteq F$ identifies the rational $\ell$-adic Tate module of the Jacobian of the quotient curve with the $G$-invariants in that of $F$, compatibly with automorphisms descending to the quotient. It is used in the construction of the maps on rational Tate modules attached to semistable coverings of modular curves of full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_injective_linearMap_rationalTateModule_fixedField_range_eq_iInf_ker_and_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_JZeroTateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem AlgebraicCurve.Pic0.exists_injective_linearMap_rationalTateModule_fixedField_range_eq_iInf_ker_and_comp_eq
    {k : Type} [Field k] [IsAlgClosed k] {F : Type} [Field F] [Algebra k F] [AlgebraicCurve.IsCurveOver k F]
    (G : Subgroup (F ≃ₐ[k] F)) [Finite G]
    [AlgebraicCurve.IsCurveOver k ↥(IntermediateField.fixedField G)]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ Φ : ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k ↥(IntermediateField.fixedField G)) →ₗ[ℚ_[ℓ]]
        ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k F),
      Function.Injective Φ ∧
      LinearMap.range Φ =
        ⨅ g : G, LinearMap.ker
          (ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k F) (F ≃ₐ[k] F) (g : F ≃ₐ[k] F) - 1) ∧
      ∀ (σ : F ≃ₐ[k] F)
        (τ : ↥(IntermediateField.fixedField G) ≃ₐ[k] ↥(IntermediateField.fixedField G)),
        (∀ y : ↥(IntermediateField.fixedField G), σ (y : F) = ((τ y : ↥(IntermediateField.fixedField G)) : F)) →
          Φ ∘ₗ ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k ↥(IntermediateField.fixedField G))
              (↥(IntermediateField.fixedField G) ≃ₐ[k] ↥(IntermediateField.fixedField G)) τ =
            ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k F) (F ≃ₐ[k] F) σ ∘ₗ Φ := by sorry
