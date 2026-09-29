-- Prove2me | Theorems.Thm_Algebra_IsStandardEtale_exists_forall_algHom_evalEval_eq_zero_and_ext_and_surj_and_repr
-- name    : Algebra.IsStandardEtale.exists_forall_algHom_evalEval_eq_zero_and_ext_and_surj_and_repr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/667f241f-a11f-5e8d-afbc-e6979ac9443f
-- title:
--   Points of a standard étale k[X]-algebra lie on a plane chart
-- statement:
--   Let $k$ be a field and let $A$ be a commutative ring carrying compatible $k$- and $k[X]$-algebra structures (the scalar tower condition over $k \subseteq k[X]$) such that $A$ is a standard étale $k[X]$-algebra in the sense of `Algebra.IsStandardEtale`. The assertion is that there exist an element $x \in A$ and two bivariate polynomials $F, G \in k[X][Y]$ with the following four properties, where for a $k$-algebra homomorphism $\tau : A \to k$ one writes $z_\tau = \tau(\mathrm{algebraMap}_{k[X],A}(X))$ and $w_\tau = \tau(x)$, and where evaluation of an element of $k[X][Y]$ at a pair of elements of $k$ is `Polynomial.evalEval`. First, for every $k$-algebra homomorphism $\tau : A \to k$ one has $F(z_\tau, w_\tau) = 0$, $G(z_\tau, w_\tau) \neq 0$ and $(\partial_Y F)(z_\tau, w_\tau) \neq 0$, the derivative being `Polynomial.derivative` taken in the outer variable $Y$. Second, $\tau$ is determined by the pair $(z_\tau, w_\tau)$: if two $k$-algebra homomorphisms $\tau, \tau' : A \to k$ agree on the image of $X$ and on $x$, they are equal. Third, every pair $(z, w) \in k^2$ with $F(z,w) = 0$ and $G(z,w) \neq 0$ arises as $(z_\tau, w_\tau)$ for some $k$-algebra homomorphism $\tau : A \to k$. Fourth, every $s \in A$ admits $h \in k[X][Y]$ and $n \in \mathbb{N}$ with $\tau(s)\, G(z_\tau, w_\tau)^n = h(z_\tau, w_\tau)$ for all $\tau$; that is, $s$ is represented on $k$-points by the regular function $h/G^n$ on the plane chart.
--
--   This is the point-set form of the local structure of standard étale morphisms: the $k$-points of a standard étale $k[X]$-algebra are identified, coordinatewise by the image of $X$ and by one further coordinate $x$, with the plane set $\{F = 0,\ G \neq 0\}$ in $k^2$, on which $\partial_Y F$ is nowhere zero and on which every element of $A$ is given by a fraction $h/G^n$. It is used to produce an explicit chart for an étale coordinate in [`Algebra.exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential`](thm.html#Algebra.exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_IsStandardEtale_exists_forall_algHom_evalEval_eq_zero_and_ext_and_surj_and_repr.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial
open scoped Polynomial.Bivariate

theorem Algebra.IsStandardEtale.exists_forall_algHom_evalEval_eq_zero_and_ext_and_surj_and_repr
    (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A]
    [Algebra.IsStandardEtale k[X] A] :
    ∃ (x : A) (F G : k[X][Y]),
      (∀ τ : A →ₐ[k] k,
        Polynomial.evalEval (τ (algebraMap k[X] A Polynomial.X)) (τ x) F = 0 ∧
        Polynomial.evalEval (τ (algebraMap k[X] A Polynomial.X)) (τ x) G ≠ 0 ∧
        Polynomial.evalEval (τ (algebraMap k[X] A Polynomial.X)) (τ x) (Polynomial.derivative F) ≠ 0) ∧
      (∀ τ τ' : A →ₐ[k] k, τ (algebraMap k[X] A Polynomial.X) = τ' (algebraMap k[X] A Polynomial.X) → τ x = τ' x → τ = τ') ∧
      (∀ z w : k, Polynomial.evalEval z w F = 0 → Polynomial.evalEval z w G ≠ 0 →
        ∃ τ : A →ₐ[k] k, τ (algebraMap k[X] A Polynomial.X) = z ∧ τ x = w) ∧
      (∀ s : A, ∃ (h : k[X][Y]) (n : ℕ), ∀ τ : A →ₐ[k] k,
        τ s * (Polynomial.evalEval (τ (algebraMap k[X] A Polynomial.X)) (τ x) G) ^ n =
          Polynomial.evalEval (τ (algebraMap k[X] A Polynomial.X)) (τ x) h) := by sorry
