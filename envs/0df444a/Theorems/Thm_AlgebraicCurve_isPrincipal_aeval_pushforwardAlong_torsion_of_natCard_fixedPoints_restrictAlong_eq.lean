-- Prove2me | Theorems.Thm_AlgebraicCurve_isPrincipal_aeval_pushforwardAlong_torsion_of_natCard_fixedPoints_restrictAlong_eq
-- name    : AlgebraicCurve.isPrincipal_aeval_pushforwardAlong_torsion_of_natCard_fixedPoints_restrictAlong_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/b1858d03-239a-5038-bf91-76150057ed61
-- title:
--   Weil: P(Fr_*) annihilates ℓ^m-torsion divisor classes
-- statement:
--   Let $k$ be a finite field, $K$ an algebraically closed field, and let $F_0$ be an algebra over $k$ and $F$ an algebra over both $K$ and $F_0$, with $F_0$ a curve over $k$ and $F$ a curve over $K$ in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero element has an associated divisor of degree $0$ recording its orders at all places, each place has residue field finite over the base field, and the module of Kähler differentials is free of rank one. Assume $F_0$ is generated over $k$ by a finite set, and that the image of $F_0$ generates $F$ over $K$. Let $\varphi \colon F \to F$ be a $K$-algebra endomorphism making $F$ integral over its image and satisfying $\varphi(x) = x^{\#k}$ on the image of $F_0$, and let $P \in \mathbb{Z}[X]$ be monic such that for every $n \ge 1$ the fixed-point set of the $n$-th iterate of the induced map $w \mapsto \varphi^{-1}(\mathcal{O}_w)$ on places of $F/K$ is finite with cardinality, as a complex number, $(\#k)^n + 1 - \sum_{\omega} \omega^n$, the sum over the complex roots of $P$ with multiplicity. Let $\ell$ be a prime invertible in $K$ and $m \in \mathbb{N}$. Then for every divisor $D$ on $F/K$ of degree $0$ such that $\ell^m \cdot D$ is principal, the divisor $P$ applied to the push-forward endomorphism [`AlgebraicCurve.Divisor.pushforwardAlong φ hφi`](def/AlgebraicCurve_Correspondence.html#L99), evaluated at $D$, is principal.
--
--   This is the $\ell$-adic form of Weil's theorem on the characteristic polynomial of the Frobenius endomorphism of the Jacobian of a curve over a finite field: the zeta numerator $P$, evaluated at the Frobenius push-forward, kills the $\ell^m$-torsion of the degree-zero divisor class group, the classical statement being Cayley–Hamilton on the Tate module read modulo $\ell^m$. It is used in the construction of Frobenius eigenvalue relations on modular curves and in the corresponding computation for Drinfeld-type curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_isPrincipal_aeval_pushforwardAlong_torsion_of_natCard_fixedPoints_restrictAlong_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.isPrincipal_aeval_pushforwardAlong_torsion_of_natCard_fixedPoints_restrictAlong_eq
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (P : Polynomial ℤ) (hP : P.Monic)
    (hcount : ∀ n : ℕ, 0 < n →
      (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[n]).Finite ∧
        (Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[n]) : ℂ) =
          (Nat.card k : ℂ) ^ n + 1 -
            (((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ n)).sum))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) (m : ℕ)
    (D : AlgebraicCurve.Divisor K F) (hD : AlgebraicCurve.Divisor.degree D = 0)
    (hDℓ : AlgebraicCurve.Divisor.IsPrincipal (((ℓ ^ m : ℕ) : ℤ) • D)) :
    AlgebraicCurve.Divisor.IsPrincipal
      (Polynomial.aeval (AlgebraicCurve.Divisor.pushforwardAlong φ hφi).toIntLinearMap P D) := by sorry
