-- Prove2me | Theorems.Thm_DrinfeldCurve_exists_rationalTateModule_linearEquiv_baseChange_of_injective_of_card_torsionBy_eq
-- name    : DrinfeldCurve.exists_rationalTateModule_linearEquiv_baseChange_of_injective_of_card_torsionBy_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/09eaa41e-6724-5d92-b498-cbda0aa13414
-- title:
--   Base change of rational Tate modules for Drinfeld curves
-- statement:
--   Let $q$ be a prime and let $k \subseteq K$ be fields with $K$ algebraic over $k$, both algebras over $\mathrm{GF}(q^2)$ compatibly (scalar tower), such that the coordinate rings `CoordRing q k` and `CoordRing q K` are domains, so that the Drinfeld function fields $F = \mathrm{Frac}(\mathrm{CoordRing}\,q\,k)$ and $F' = \mathrm{Frac}(\mathrm{CoordRing}\,q\,K)$ are defined and $F'$ is an $F$-algebra through the constants map. Assume `HasPrincipalDivisors K F'`, i.e. every nonzero element of $F'$ is the divisor of a degree-zero divisor recording its order at each place, and `ConstantFieldDegreeFormula`, i.e. pullback of constants along $k \to K$ preserves the degree of divisors. Write $J = \mathrm{Pic}^0(k,F)$ and $J' = \mathrm{Pic}^0(K,F')$ for the groups of degree-zero divisors modulo principal divisors, and let $\beta$ = `Pic0.baseChange` be the induced homomorphism $J \to J'$. Assume $\beta$ is injective, let $\ell$ be a prime and $r$ a natural number, and assume that for every $n$ the subgroups of $J$ and of $J'$ killed by $\ell^n$ both have exactly $(\ell^n)^r$ elements. Then there is a $\mathbb{Q}_\ell$-linear isomorphism $e$ from $\mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} T_\ell J$ onto $\mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} T_\ell J'$ which agrees pointwise with `vpMap`, the $\mathbb{Q}_\ell$-base change of the map on Tate modules induced by $\beta$, and which satisfies $e \circ \rho_J(h) = \rho_{J'}(h) \circ e$ for every $h$ in `hSubgroup q`, the kernel of `hChar q` in $\mathrm{GL}_2(\mathbb{Z}/q) \times \mathrm{GF}(q^2)^\times$, acting on $J$ and $J'$ through the automorphisms `hFunctionFieldAction q k h` of $F/k$ and `hFunctionFieldAction q K h` of $F'/K$.
--
--   This is the comparison, for the Drinfeld curve, between the rational $\ell$-adic Tate module of its degree-zero divisor class group over a base field and over an algebraic extension: under equality of $\ell$-power torsion counts the base-change map becomes an isomorphism after tensoring with $\mathbb{Q}_\ell$, equivariantly for the action of the finite group `hSubgroup q`. It is used in the analysis of intertwining maps for cuspidal representations attached to the Drinfeld curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DrinfeldCurve_exists_rationalTateModule_linearEquiv_baseChange_of_injective_of_card_torsionBy_eq.lean

import Definitions.Def_AlgebraicCurve_Pic0BaseChange
import Definitions.Def_DrinfeldCurve_MapConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve DrinfeldCurve
attribute [local instance 10] constantsAlgebraCoordRing functionFieldConstantsAlgebra in
attribute [local instance] isIntegral_functionFieldMapConstants in

theorem DrinfeldCurve.exists_rationalTateModule_linearEquiv_baseChange_of_injective_of_card_torsionBy_eq
    (q : ℕ) [Fact q.Prime] (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [Algebra (GaloisField q 2) k] [Algebra (GaloisField q 2) K] [IsScalarTower (GaloisField q 2) k K]
    [IsDomain (CoordRing q k)] [IsDomain (CoordRing q K)] [HasPrincipalDivisors K (drinfeldFunctionField q K)]
    [ConstantFieldDegreeFormula k K (drinfeldFunctionField q k) (drinfeldFunctionField q K)]
    (hβ : Function.Injective (Pic0.baseChange k K (drinfeldFunctionField q k) (drinfeldFunctionField q K)))
    (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ)
    (hJ : ∀ n : ℕ,
      Nat.card (Submodule.torsionBy ℤ (Pic0 k (drinfeldFunctionField q k)) ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ r)
    (hJ' : ∀ n : ℕ,
      Nat.card (Submodule.torsionBy ℤ (Pic0 K (drinfeldFunctionField q K)) ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ r) :
    ∃ e : ModularCurve.RationalTateModule ℓ (Pic0 k (drinfeldFunctionField q k)) ≃ₗ[ℚ_[ℓ]]
        ModularCurve.RationalTateModule ℓ (Pic0 K (drinfeldFunctionField q K)),
      (∀ v,
        e v = ModularCurve.vpMap ℓ (Pic0.baseChange k K (drinfeldFunctionField q k) (drinfeldFunctionField q K)) v) ∧
        ∀ h : hSubgroup q,
          (e : ModularCurve.RationalTateModule ℓ (Pic0 k (drinfeldFunctionField q k)) →ₗ[ℚ_[ℓ]]
              ModularCurve.RationalTateModule ℓ (Pic0 K (drinfeldFunctionField q K))) ∘ₗ
            ModularCurve.rationalGaloisRep ℓ (Pic0 k (drinfeldFunctionField q k))
              (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) (hFunctionFieldAction q k h) =
          ModularCurve.rationalGaloisRep ℓ (Pic0 K (drinfeldFunctionField q K))
              (drinfeldFunctionField q K ≃ₐ[K] drinfeldFunctionField q K) (hFunctionFieldAction q K h) ∘ₗ
            (e : ModularCurve.RationalTateModule ℓ (Pic0 k (drinfeldFunctionField q k)) →ₗ[ℚ_[ℓ]]
              ModularCurve.RationalTateModule ℓ (Pic0 K (drinfeldFunctionField q K))) := by sorry
