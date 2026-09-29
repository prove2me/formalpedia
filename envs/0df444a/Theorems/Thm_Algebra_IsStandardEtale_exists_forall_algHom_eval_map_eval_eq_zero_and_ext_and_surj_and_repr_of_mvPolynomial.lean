-- Prove2me | Theorems.Thm_Algebra_IsStandardEtale_exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial
-- name    : Algebra.IsStandardEtale.exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/6135800e-ab33-5d70-91f3-2c31cecdcfb1
-- title:
--   Points of a standard étale algebra over k[X₁,…,Xₙ]
-- statement:
--   Let $k$ be a field, $n\in\mathbb{N}$, and let $A$ be a commutative ring that is simultaneously a $k$-algebra and an algebra over $R=k[X_1,\dots,X_n]=$ `MvPolynomial (Fin n) k`, the two structures being compatible (scalar tower $k\to R\to A$), and assume $A$ is a standard étale $R$-algebra. For a $k$-algebra homomorphism $\tau : A\to k$ write $z_\tau = (\tau(\text{image of } X_i))_{i<n}\in k^n$, and for $q\in R[Y]$ write $q(z,w)$ for the value at $w\in k$ of the polynomial obtained from $q$ by applying $\mathrm{eval}\,z$ to its coefficients. The assertion is that there exist $x\in A$ and $F,G\in R[Y]$ such that: (i) for every $\tau\in\operatorname{Hom}_{k\text{-alg}}(A,k)$ one has $F(z_\tau,\tau x)=0$, $G(z_\tau,\tau x)\neq 0$ and $(\partial_Y F)(z_\tau,\tau x)\neq 0$; (ii) two such $\tau,\tau'$ agreeing on the images of all $X_i$ and with $\tau x=\tau' x$ are equal; (iii) every pair $(z,w)\in k^n\times k$ with $F(z,w)=0$ and $G(z,w)\neq 0$ arises as $(z_\tau,\tau x)$ for some $\tau$; (iv) for every $s\in A$ there are $h\in R[Y]$ and $N\in\mathbb{N}$, independent of $\tau$, with $\tau(s)\,G(z_\tau,\tau x)^N = h(z_\tau,\tau x)$ for all $\tau$.
--
--   This is the description of the $k$-points of a standard étale algebra $A$ over an $n$-variable polynomial ring as the set of pairs $(z,w)$ with $F(z,w)=0$, $G(z,w)\neq 0$, together with the representation of each element of $A$ as $h/G^N$; it is the several-variable form of the one-variable statement. It is used to produce analytic charts, in [`Algebra.exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential`](thm.html#Algebra.exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_IsStandardEtale_exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Algebra.IsStandardEtale.exists_forall_algHom_eval_map_eval_eq_zero_and_ext_and_surj_and_repr_of_mvPolynomial
    (k : Type) [Field k] {n : ℕ} (A : Type) [CommRing A] [Algebra k A] [Algebra (MvPolynomial (Fin n) k) A]
    [IsScalarTower k (MvPolynomial (Fin n) k) A] [Algebra.IsStandardEtale (MvPolynomial (Fin n) k) A] :
    ∃ (x : A) (F G : Polynomial (MvPolynomial (Fin n) k)),
      (∀ τ : A →ₐ[k] k,
        (F.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x) = 0 ∧
        (G.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x) ≠ 0 ∧
        ((Polynomial.derivative F).map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x) ≠ 0) ∧
      (∀ τ τ' : A →ₐ[k] k,
        (∀ i : Fin n, τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)) =
          τ' (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i))) → τ x = τ' x → τ = τ') ∧
      (∀ (z : Fin n → k) (w : k), (F.map (MvPolynomial.eval z)).eval w = 0 → (G.map (MvPolynomial.eval z)).eval w ≠ 0 →
        ∃ τ : A →ₐ[k] k, (∀ i : Fin n, τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)) = z i) ∧ τ x = w) ∧
      (∀ s : A, ∃ (h : Polynomial (MvPolynomial (Fin n) k)) (N : ℕ), ∀ τ : A →ₐ[k] k,
        τ s * ((G.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x)) ^ N =
          (h.map (MvPolynomial.eval fun i : Fin n => τ (algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)))).eval (τ x)) := by sorry
