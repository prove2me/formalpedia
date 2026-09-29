-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_weilPairing
-- name    : AlgebraicCurve.Pic0.exists_weilPairing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/edb0e6a6-a125-5782-a401-5777a10df200
-- title:
--   Existence of the Weil pairing on Pic⁰[n]
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and let $F$ be a $K$-algebra which is a field, subject to the hypothesis that some $x \in F$ is transcendental over $K$ with $F$ finite-dimensional over $K(x)$, and satisfying `IsCurveOver K F`: every nonzero $f \in F$ has a divisor of degree $0$ recording its orders $v(f)$ at all places, each place has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank $1$ over $F$. Write $\mathrm{Pic}^0 =$ `Pic0 K F` for the degree-zero divisors modulo principal ones. Then there is a family of maps $e_n : \mathrm{Pic}^0 \times \mathrm{Pic}^0 \to K$, indexed by $n \in \mathbb{N}$, such that for all $n > 0$ and all elements killed by $n$: $e_n(x,y)^n = 1$; $e_n$ is additive in each argument separately; $e_n$ is non-degenerate on each side, i.e. $e_n(x,\cdot) \equiv 1$ on the $n$-torsion forces $x = 0$, and symmetrically; for $x,y$ killed by $nm$ with $n,m > 0$, $e_n(mx,my) = e_{nm}(x,y)^m$; for $g$ in `SemilinearAut K F`, the group of pairs $(\sigma,\tau) \in \mathrm{Aut}(F) \times \mathrm{Aut}(K)$ with $\sigma \circ \mathrm{alg} = \mathrm{alg} \circ \tau$, one has $e_n(g x, g y) = \tau(e_n(x,y))$; and, for any field $F'$ over $K$ with principal divisors and any two $K$-algebra maps $\varphi, \psi : F \to F'$ that are integral and satisfy the fundamental-identity, finiteness and norm-formula hypotheses needed for pullback and pushforward of degree-zero classes (for both $\varphi$ and $\psi$), the correspondence $\psi_* \varphi^*$ and the correspondence $\varphi_* \psi^*$ are adjoint: $e_n(\psi_*\varphi^* x, y) = e_n(x, \varphi_*\psi^* y)$. Nothing is asserted about the values of $e_n$ outside the $n$-torsion.
--
--   This is the Weil pairing $e_n$ on the $n$-torsion of the Jacobian of a curve over an algebraically closed field of characteristic zero, presented in the divisor-class language of function fields, together with its standard properties: $\mu_n$-values, biadditivity, perfectness, compatibility under $n \mapsto nm$, Galois (semilinear) equivariance, and adjunction of correspondences. It is used on modular curves to produce the pairings on Tate modules on which the Hecke operators are self-adjoint and Galois acts through the cyclotomic character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_weilPairing.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.exists_weilPairing (K F : Type*) [Field K] [Field F] [Algebra K F]
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
          = e n x (Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ y)) := by sorry
