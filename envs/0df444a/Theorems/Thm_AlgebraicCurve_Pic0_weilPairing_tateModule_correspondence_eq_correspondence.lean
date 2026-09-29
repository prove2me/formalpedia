-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_weilPairing_tateModule_correspondence_eq_correspondence
-- name    : AlgebraicCurve.Pic0.weilPairing_tateModule_correspondence_eq_correspondence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/a73b8593-d287-5b58-8f85-a5f173e1ff66
-- title:
--   Correspondence and its transpose are adjoint on T_ℓ Pic⁰
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and $F$ a field extension of $K$ which is finitely generated of transcendence degree one in the explicit sense assumed here (there exists $x \in F$ transcendental over $K$ with $F$ finite-dimensional over $K(x)$), and assume `IsCurveOver K F`: every nonzero $f \in F$ has a degree-zero divisor recording its orders at all places, every residue field of a place is finite-dimensional over $K$, and $\Omega_{F/K}$ is free of rank one over $F$. Let $\ell$ be a prime and let $\zeta : \mathbb{N} \to K$ be a compatible system of roots of unity, $\zeta_n$ a primitive $\ell^n$-th root of unity with $\zeta_{n+1}^{\ell} = \zeta_n$. Write $\mathrm{Pic}^0(K,F)$ for the group of degree-zero divisors modulo principal divisors and $T_\ell$ for its Tate module, the group of sequences $(x_n)_{n}$ in $\mathrm{Pic}^0(K,F)$ with $\ell^n x_n = 0$ and $\ell\, x_{n+1} = x_n$. Let $e : T_\ell \times T_\ell \to \mathbb{Z}_\ell$ be $\mathbb{Z}_\ell$-bilinear and assume that it reads the divisorial Weil pairings levelwise: for every $n$, every `DivisorialWeilPairingData K F (ℓ^n)` $W$ (a $K$-valued pairing on the $\ell^n$-torsion of $\mathrm{Pic}^0$ compatible with the pairings of Weil data and satisfying the stated moving property), all $a, b \in T_\ell$ and all $a', b'$ in the $\ell^n$-torsion whose underlying classes are $a_n$ and $b_n$, one has $W(a',b') = \zeta_n^{\,m}$ with $m$ the $n$-th natural-number approximation of $e(a,b)$. Let $F'$ be a field extension of $K$ in which every nonzero element has such a divisor, and let $\varphi, \psi : F \to F'$ be $K$-algebra maps that are integral, finite, and satisfy the fundamental identity and the pushforward norm formula along each. Let $C, C' : T_\ell \to T_\ell$ be $\mathbb{Z}_\ell$-linear maps acting in each level $n$ by the endomorphisms $\psi_* \circ \varphi^*$ and $\varphi_* \circ \psi^*$ of $\mathrm{Pic}^0(K,F)$ respectively. Then $e(Ca, b) = e(a, C'b)$ for all $a, b \in T_\ell$.
--
--   This is the $\ell$-adic form of the adjointness of a correspondence and its transpose for the Weil pairing: the endomorphism $\psi_* \varphi^*$ of $\mathrm{Pic}^0$ and its transpose $\varphi_* \psi^*$ are adjoint for the $\mathbb{Z}_\ell$-valued pairing on the Tate module. It feeds the construction of a Hecke-selfadjoint bilinear form on the Tate module of the modular curve, where the Hecke operators arise from degeneracy maps of this correspondence shape.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_weilPairing_tateModule_correspondence_eq_correspondence.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.weilPairing_tateModule_correspondence_eq_correspondence
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

    {F' : Type} [Field F'] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFIφ : FundamentalIdentityAlong K φ hφ) (hfinψ : FiniteAlong K ψ)
    (hNψ : NormFormulaAlong K ψ hfinψ)
    (hFIψ : FundamentalIdentityAlong K ψ hψ) (hfinφ : FiniteAlong K φ)
    (hNφ : NormFormulaAlong K φ hfinφ)

    (C : TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F))
    (hC : ∀ (a : TateModule ℓ (Pic0 K F)) (n : ℕ),
        ((C a : TateModule ℓ (Pic0 K F)) : ℕ → Pic0 K F) n =
          Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ ((a : ℕ → Pic0 K F) n))
    (C' : TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F))
    (hC' : ∀ (b : TateModule ℓ (Pic0 K F)) (n : ℕ),
        ((C' b : TateModule ℓ (Pic0 K F)) : ℕ → Pic0 K F) n =
          Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ ((b : ℕ → Pic0 K F) n))
    (a b : TateModule ℓ (Pic0 K F)) :
    e (C a) b = e a (C' b) := by sorry
