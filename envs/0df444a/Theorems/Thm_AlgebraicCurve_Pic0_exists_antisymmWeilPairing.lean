-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_antisymmWeilPairing
-- name    : AlgebraicCurve.Pic0.exists_antisymmWeilPairing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/4e7734de-3d05-5a29-b2c1-113edd57cfab
-- title:
--   Antisymmetric Weil pairing on the torsion of Pic⁰
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and let $F$ be a $K$-algebra which is a field, assumed to contain an element $x$ transcendental over $K$ with $F$ finite-dimensional over $K(x)$, and to satisfy `IsCurveOver K F`: every nonzero element of $F$ has a degree-zero divisor recording its orders at all places, each residue field of a place is finite-dimensional over $K$, and $\Omega[F/K]$ is free of rank $1$ over $F$. Here $\mathrm{Pic}^0(K,F)$ is the group of degree-zero divisors modulo principal divisors. Then there exists a family $e : \mathbb{N} \to \mathrm{Pic}^0 \times \mathrm{Pic}^0 \to K$ such that, for every $n > 0$ and all elements killed by $n$: $e_n(x,y)^n = 1$; $e_n$ is additive in each argument; $e_n$ is non-degenerate in each argument separately (if $e_n(x,y)=1$ for all $n$-torsion $y$ then $x=0$, and symmetrically); for $x,y$ killed by $nm$ one has $e_n(mx,my) = e_{nm}(x,y)^m$; for every element $g$ of the group of pairs $(g_F,g_K)$ of ring automorphisms compatible with $K \to F$, $e_n(gx,gy) = g_K(e_n(x,y))$; for a second field extension $F'$ of $K$ with principal divisors and two $K$-algebra maps $\varphi,\psi : F \to F'$ integral and satisfying the fundamental identity, finiteness and push-forward norm formula hypotheses in both orders, the correspondences $\psi_* \varphi^*$ and $\varphi_* \psi^*$ on $\mathrm{Pic}^0$ are adjoint for $e_n$; and $e_n(x,y)\,e_n(y,x) = 1$. Values of $e_n$ outside the $n$-torsion are unconstrained.
--
--   This is Weil's pairing $e_n$ on the $n$-torsion of the degree-zero divisor class group of a curve over an algebraically closed field of characteristic $0$, in the form used later for Tate modules: $\mu_n$-valued, biadditive, non-degenerate on both sides, compatible under multiplication by $m$, equivariant for semilinear automorphisms, adjoint for correspondences, and antisymmetric. It is invoked for the similitude properties of the pairing on the rational Tate module of the Jacobian of a modular curve, in the diamond-operator and Frobenius statements for $J_H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_antisymmWeilPairing.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.exists_antisymmWeilPairing (K F : Type*) [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] :
    ∃ e : ℕ → Pic0 K F → Pic0 K F → K,
      (∀ (n : ℕ) (x y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 → e n x y ^ n = 1) ∧
      (∀ (n : ℕ) (x x' y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • x' = 0 → (n : ℤ) • y = 0 →
        e n (x + x') y = e n x y * e n x' y) ∧
      (∀ (n : ℕ) (x y y' : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 → (n : ℤ) • y' = 0 →
        e n x (y + y') = e n x y * e n x y') ∧
      (∀ (n : ℕ) (x : Pic0 K F), 0 < n → (n : ℤ) • x = 0 →
        (∀ y : Pic0 K F, (n : ℤ) • y = 0 → e n x y = 1) → x = 0) ∧
      (∀ (n : ℕ) (y : Pic0 K F), 0 < n → (n : ℤ) • y = 0 →
        (∀ x : Pic0 K F, (n : ℤ) • x = 0 → e n x y = 1) → y = 0) ∧
      (∀ (n m : ℕ) (x y : Pic0 K F), 0 < n → 0 < m →
        ((n * m : ℕ) : ℤ) • x = 0 → ((n * m : ℕ) : ℤ) • y = 0 →
        e n ((m : ℤ) • x) ((m : ℤ) • y) = e (n * m) x y ^ m) ∧
      (∀ (n : ℕ) (g : SemilinearAut K F) (x y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
        e n (g • x) (g • y) = SemilinearAut.baseAut g (e n x y)) ∧
      (∀ (F' : Type*) [Field F'] [Algebra K F'] [HasPrincipalDivisors K F']
        (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
        (hFIφ : FundamentalIdentityAlong K φ hφ) (hfinψ : FiniteAlong K ψ)
        (hNψ : NormFormulaAlong K ψ hfinψ)
        (hFIψ : FundamentalIdentityAlong K ψ hψ) (hfinφ : FiniteAlong K φ)
        (hNφ : NormFormulaAlong K φ hfinφ)
        (n : ℕ) (x y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
        e n (Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ x) y
          = e n x (Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ y)) ∧
      (∀ (n : ℕ) (x y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
        e n x y * e n y x = 1) := by sorry
