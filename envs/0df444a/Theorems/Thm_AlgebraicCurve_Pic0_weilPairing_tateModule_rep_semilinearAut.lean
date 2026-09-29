-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_weilPairing_tateModule_rep_semilinearAut
-- name    : AlgebraicCurve.Pic0.weilPairing_tateModule_rep_semilinearAut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/bd11ba8f-df87-50d6-b368-e1d132ab2910
-- title:
--   Semilinear equivariance of the ℓ-adic Weil pairing
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and $F$ a field extension of $K$ admitting an element $x$ transcendental over $K$ with $F$ finite-dimensional over $K(x)$, and assume `IsCurveOver K F`, i.e. every nonzero element of $F$ has a divisor of degree $0$ supported on the places of $F/K$, every place has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank $1$ over $F$. Let $\ell$ be a prime and let $\zeta : \mathbb{N} \to K$ satisfy that $\zeta_n$ is a primitive $\ell^n$-th root of unity for every $n$ and $\zeta_{n+1}^{\ell} = \zeta_n$. Here $\mathrm{Pic}^0(K,F)$ is the quotient of the degree-zero divisors by the principal ones, and [`TateModule ℓ (Pic0 K F)`](def/EllipticCurve_TateModule.html#L15) is the group of sequences $a : \mathbb{N} \to \mathrm{Pic}^0$ with $\ell^n a_n = 0$ and $\ell\, a_{n+1} = a_n$. Let $e$ be a $\mathbb{Z}_\ell$-bilinear form on this Tate module such that, for every $n$, every structure `DivisorialWeilPairingData K F (ℓ ^ n)` $W$ (a pairing `W.pair` on $\mathrm{Pic}^0[\ell^n]$ with values in $K$, compatible with the pairings attached to Weil data and satisfying a moving property for representing divisors), all $a,b$ in the Tate module and all $a',b' \in \mathrm{Pic}^0[\ell^n]$ with $a' = a_n$ and $b' = b_n$, one has $W.\mathrm{pair}(a',b') = \zeta_n^{(e(a,b)).\mathrm{appr}\,n}$, the exponent being the canonical natural-number approximation of $e(a,b)$ modulo $\ell^n$. Let $g$ be a semilinear automorphism, that is, a pair consisting of a ring automorphism of $F$ and one of $K$ compatible under $K \to F$, with second component $\mathrm{baseAut}\,g$, and let $\chi \in \mathbb{Z}_\ell$ satisfy $\mathrm{baseAut}\,g(\zeta_n) = \zeta_n^{\chi \bmod \ell^n}$ for all $n$. Then for all $a,b$ in the Tate module, $e(g a, g b) = \chi\, e(a,b)$, where $g$ acts levelwise through [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174).
--
--   This is the $\ell$-adic form of Galois equivariance of the Weil pairing on the Jacobian of a curve: the pairing is equivariant for a semilinear automorphism up to the value of the cyclotomic character $\chi$ on the chosen compatible system of $\ell$-power roots of unity. It is used in the analysis of Tate modules of Jacobians of modular curves, in particular in the study of toric and old lattices and of self-adjointness of Hecke operators for bilinear forms on such Tate modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_weilPairing_tateModule_rep_semilinearAut.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.weilPairing_tateModule_rep_semilinearAut
    (K F : Type) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (ζ : ℕ → K) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n)

    (e : TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he : ∀ (n : ℕ) (W : DivisorialWeilPairingData K F (ℓ ^ n))
        (a b : TateModule ℓ (Pic0 K F)) (a' b' : Pic0.torsion K F (ℓ ^ n)),
        (a' : Pic0 K F) = (a : ℕ → Pic0 K F) n →
        (b' : Pic0 K F) = (b : ℕ → Pic0 K F) n →
        W.pair a' b' = ζ n ^ ((e a b).appr n))

    (g : SemilinearAut K F) (χ : ℤ_[ℓ])
    (hχ : ∀ n : ℕ, SemilinearAut.baseAut g (ζ n) = ζ n ^ (PadicInt.toZModPow n χ).val)
    (a b : TateModule ℓ (Pic0 K F)) :
    e (TateModule.rep ℓ (Pic0 K F) (SemilinearAut K F) g a)
        (TateModule.rep ℓ (Pic0 K F) (SemilinearAut K F) g b) = χ * e a b := by sorry
