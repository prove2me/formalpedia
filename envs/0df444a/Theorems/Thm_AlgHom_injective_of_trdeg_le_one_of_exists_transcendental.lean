-- Prove2me | Theorems.Thm_AlgHom_injective_of_trdeg_le_one_of_exists_transcendental
-- name    : AlgHom.injective_of_trdeg_le_one_of_exists_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/6add587d-1f0c-59a7-8e01-cad30280b935
-- title:
--   Injectivity of algebra maps from domains of transcendence degree ≤ 1
-- statement:
--   Let $k$ be a field, let $D$ be a commutative ring which is an integral domain and a $k$-algebra, let $L$ be a commutative ring which is an integral domain and a $k$-algebra, and let $E$ be a commutative $k$-algebra (no domain hypothesis on $E$). Suppose given a $k$-algebra homomorphism $\Theta\colon D \to L$ which is injective as a function, and suppose the transcendence degree $\operatorname{trdeg}_k L$ (as a cardinal) satisfies $\operatorname{trdeg}_k L \le 1$. Let $\Psi\colon D \to E$ be a $k$-algebra homomorphism for which there exists an element $d \in D$ such that $\Psi(d)$ is transcendental over $k$, i.e. $\Psi(d)$ is not algebraic over $k$ as an element of $E$. The conclusion is that $\Psi$ is injective as a function. Thus a domain that embeds over $k$ into a domain of transcendence degree at most one admits no non-injective $k$-algebra map to a commutative $k$-algebra which takes at least one value transcendental over $k$.
--
--   A purely algebraic rigidity statement: over a base $k$, a domain of transcendence degree at most one has no proper quotients supporting a transcendental element. It is used in the construction of the models of modular curves, in the two results producing a domain together with ring maps to a function field and to the field of modular functions, where it rules out a kernel for the map under consideration.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgHom_injective_of_trdeg_le_one_of_exists_transcendental.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgHom.injective_of_trdeg_le_one_of_exists_transcendental
    {k D L E : Type*} [Field k] [CommRing D] [IsDomain D] [Algebra k D]
    [CommRing L] [IsDomain L] [Algebra k L] [CommRing E] [Algebra k E]
    (Θ : D →ₐ[k] L) (hΘ : Function.Injective Θ) (hL : Algebra.trdeg k L ≤ 1)
    (Ψ : D →ₐ[k] E) (hΨ : ∃ d : D, Transcendental k (Ψ d)) :
    Function.Injective Ψ := by sorry
