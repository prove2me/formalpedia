-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_weilPairing_tateModule_apply_eq_of_forall_pair_eq
-- name    : AlgebraicCurve.Pic0.weilPairing_tateModule_apply_eq_of_forall_pair_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/c12c4894-866f-539c-969f-ecc467e296c6
-- title:
--   Levelwise adjointness passes to the ℓ-adic Weil pairings
-- statement:
--   Let $K$ be a field and let $F,F'$ be $K$-algebras that are fields in which every nonzero element has a divisor of degree zero (the class `HasPrincipalDivisors`), so that the degree-zero divisor class groups $\mathrm{Pic}^0(K,F)$ and $\mathrm{Pic}^0(K,F')$ — degree-zero divisors on places modulo principal divisors — are defined. Let $\ell$ be a prime and $\zeta\colon\mathbb{N}\to K$ a family with $\zeta_n$ a primitive $\ell^n$-th root of unity for every $n$. Write $T_\ell$ for the Tate module, the group of sequences $(x_n)$ with $\ell^n x_n=0$ and $\ell\,x_{n+1}=x_n$. Assume given $\mathbb{Z}_\ell$-bilinear forms $e$ on $T_\ell\,\mathrm{Pic}^0(K,F)$ and $e'$ on $T_\ell\,\mathrm{Pic}^0(K,F')$ such that for every $n$, every `DivisorialWeilPairingData` $W$ of order $\ell^n$ on $F$ (a pairing `pair` on the $\ell^n$-torsion of $\mathrm{Pic}^0$ with values in $K$, compatible with the pairing attached to each Weil datum, and satisfying the `move` property on representatives) and every $a,b$, one has $W.\mathrm{pair}(a_n,b_n)=\zeta_n^{\,(e(a,b)).\mathrm{appr}\,n}$, and likewise for $e'$ and data $W'$ on $F'$; assume such data exist at every level on both sides. Let $S\colon\mathrm{Pic}^0(K,F)\to\mathrm{Pic}^0(K,F')$ and $T$ in the opposite direction be additive maps which are adjoint at every level, $W'.\mathrm{pair}(Sx,y)=W.\mathrm{pair}(x,Ty)$ for all levels and all data, and let $CS,CT$ be $\mathbb{Z}_\ell$-linear maps on the Tate modules acting levelwise by $S$ and $T$. Then $e'(CS\,a,b)=e(a,CT\,b)$ for all $a,b$.
--
--   This is the passage to the $\ell$-adic limit of the finite-level adjunction between two Jacobians (property I of the Weil pairing in the classical theory): maps adjoint for all the divisorial Weil pairings of order $\ell^n$ induce adjoint maps for the $\ell$-adic pairings on Tate modules. It is used in the analysis of the Jacobian of a modular curve at $p$, in the statements about pushforward–pullback pairs and the toric and old lattices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_weilPairing_tateModule_apply_eq_of_forall_pair_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.weilPairing_tateModule_apply_eq_of_forall_pair_eq
    (K F F' : Type) [Field K] [Field F] [Algebra K F] [Field F'] [Algebra K F']
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (ℓ : ℕ) [Fact ℓ.Prime]
    (ζ : ℕ → K) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n))

    (e : TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he : ∀ (n : ℕ) (W : DivisorialWeilPairingData K F (ℓ ^ n))
        (a b : TateModule ℓ (Pic0 K F)) (a' b' : Pic0.torsion K F (ℓ ^ n)),
        (a' : Pic0 K F) = (a : ℕ → Pic0 K F) n →
        (b' : Pic0 K F) = (b : ℕ → Pic0 K F) n →
        W.pair a' b' = ζ n ^ ((e a b).appr n))
    (e' : TateModule ℓ (Pic0 K F') →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F') →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he' : ∀ (n : ℕ) (W' : DivisorialWeilPairingData K F' (ℓ ^ n))
        (a b : TateModule ℓ (Pic0 K F')) (a' b' : Pic0.torsion K F' (ℓ ^ n)),
        (a' : Pic0 K F') = (a : ℕ → Pic0 K F') n →
        (b' : Pic0 K F') = (b : ℕ → Pic0 K F') n →
        W'.pair a' b' = ζ n ^ ((e' a b).appr n))

    (hW : ∀ n : ℕ, Nonempty (DivisorialWeilPairingData K F (ℓ ^ n)))
    (hW' : ∀ n : ℕ, Nonempty (DivisorialWeilPairingData K F' (ℓ ^ n)))

    (S : Pic0 K F →+ Pic0 K F') (T : Pic0 K F' →+ Pic0 K F)
    (hST : ∀ (n : ℕ) (W : DivisorialWeilPairingData K F (ℓ ^ n))
        (W' : DivisorialWeilPairingData K F' (ℓ ^ n))
        (x Ty : Pic0.torsion K F (ℓ ^ n)) (Sx y : Pic0.torsion K F' (ℓ ^ n)),
        (Sx : Pic0 K F') = S (x : Pic0 K F) →
        (Ty : Pic0 K F) = T (y : Pic0 K F') →
        W'.pair Sx y = W.pair x Ty)

    (CS : TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F'))
    (hCS : ∀ (a : TateModule ℓ (Pic0 K F)) (n : ℕ),
        ((CS a : TateModule ℓ (Pic0 K F')) : ℕ → Pic0 K F') n = S ((a : ℕ → Pic0 K F) n))
    (CT : TateModule ℓ (Pic0 K F') →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F))
    (hCT : ∀ (b : TateModule ℓ (Pic0 K F')) (n : ℕ),
        ((CT b : TateModule ℓ (Pic0 K F)) : ℕ → Pic0 K F) n = T ((b : ℕ → Pic0 K F') n))
    (a : TateModule ℓ (Pic0 K F)) (b : TateModule ℓ (Pic0 K F')) :
    e' (CS a) b = e a (CT b) := by sorry
