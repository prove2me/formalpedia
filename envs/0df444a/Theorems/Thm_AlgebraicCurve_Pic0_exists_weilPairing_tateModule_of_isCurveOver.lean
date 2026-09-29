-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_weilPairing_tateModule_of_isCurveOver
-- name    : AlgebraicCurve.Pic0.exists_weilPairing_tateModule_of_isCurveOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/67c39188-92fd-5551-9b58-ffcb4f662c6c
-- title:
--   ℓ-adic Weil pairing on the Tate module of Pic⁰
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, $K$ algebraically closed of characteristic zero, and assume some $x \in F$ is transcendental over $K$ with $F$ finite-dimensional over $K(x)$; assume moreover `IsCurveOver K F`, i.e. every nonzero $f \in F$ has a divisor (a finitely supported integer-valued function on the places of $F/K$, the places being proper valuation subrings of $F$ containing $K$ that are principal ideal rings) recording its orders and having degree zero, every residue field of a place is finite over $K$, and $\Omega_{F/K}$ is free of rank $1$ over $F$. Let $\ell$ be a prime and let $\zeta_n \in K$ be a primitive $\ell^n$-th root of unity for each $n$ with $\zeta_{n+1}^{\ell} = \zeta_n$. Write $\mathrm{Pic}^0 = \mathrm{Pic}^0(K,F)$ for the degree-zero divisors modulo principal ones, and $T = T_\ell(\mathrm{Pic}^0)$ for the group of sequences $(a_n)_n$ in $\mathrm{Pic}^0$ with $\ell^n a_n = 0$ and $\ell\, a_{n+1} = a_n$. Then there exists a $\mathbb{Z}_\ell$-bilinear map $e \colon T \times T \to \mathbb{Z}_\ell$ such that: for every $n$, every datum $W$ of type `DivisorialWeilPairingData K F (ℓ ^ n)` (a pairing on the $\ell^n$-torsion of $\mathrm{Pic}^0$ with values in $K$, compatible with the expression $f_1(D_2)/f_2(D_1)$ on Weil data of order $\ell^n$ and admitting representatives with rational support avoiding any prescribed finite set of places), and all $a,b \in T$ and $\ell^n$-torsion classes $a',b'$ equal in $\mathrm{Pic}^0$ to $a_n$ and $b_n$ respectively, one has $W.\mathrm{pair}(a',b') = \zeta_n^{\,c}$ where $c$ is the natural number approximation `(e a b).appr n` of $e(a,b)$ modulo $\ell^n$; $e(b,a) = -e(a,b)$; and $e(a,b) = 0$ for all $b$ forces $a = 0$.
--
--   This is the $\ell$-adic Weil pairing on the Tate module of the Jacobian of a curve, built as the inverse limit of the divisorial Weil pairings on the $\ell^n$-torsion of $\mathrm{Pic}^0$, with values transported to $\mathbb{Z}_\ell$ through the chosen compatible system of $\ell$-power roots of unity; alternation and non-degeneracy over $\mathbb{Z}_\ell$ are recorded alongside. It is used in the analysis of lattices in Tate modules of Jacobians of modular curves, where orthogonality for this pairing controls membership in the span of degeneracy maps and inertia augmentations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_weilPairing_tateModule_of_isCurveOver.lean

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

theorem AlgebraicCurve.Pic0.exists_weilPairing_tateModule_of_isCurveOver
    (K F : Type) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (ζ : ℕ → K) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n) :
    ∃ e : TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 K F) →ₗ[ℤ_[ℓ]] ℤ_[ℓ],

      (∀ (n : ℕ) (W : DivisorialWeilPairingData K F (ℓ ^ n))
          (a b : TateModule ℓ (Pic0 K F)) (a' b' : Pic0.torsion K F (ℓ ^ n)),
          (a' : Pic0 K F) = (a : ℕ → Pic0 K F) n →
          (b' : Pic0 K F) = (b : ℕ → Pic0 K F) n →
          W.pair a' b' = ζ n ^ ((e a b).appr n)) ∧

      (∀ a b : TateModule ℓ (Pic0 K F), e b a = -(e a b)) ∧

      (∀ a : TateModule ℓ (Pic0 K F), (∀ b : TateModule ℓ (Pic0 K F), e a b = 0) → a = 0) := by sorry
