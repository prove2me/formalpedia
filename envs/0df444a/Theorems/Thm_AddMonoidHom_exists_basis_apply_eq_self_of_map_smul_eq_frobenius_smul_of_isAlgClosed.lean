-- Prove2me | Theorems.Thm_AddMonoidHom_exists_basis_apply_eq_self_of_map_smul_eq_frobenius_smul_of_isAlgClosed
-- name    : AddMonoidHom.exists_basis_apply_eq_self_of_map_smul_eq_frobenius_smul_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/219ef6e1-7def-5054-8305-22b4963e45aa
-- title:
--   Triviality of unit-root F-crystals over W(k), k algebraically closed
-- statement:
--   Let $p$ be a prime and let $k$ be an algebraically closed field of characteristic $p$, so that the ring $W(p,k)$ of $p$-typical Witt vectors of $k$ carries its Frobenius endomorphism `WittVector.frobenius`, acting on Witt coordinates by raising them to the $p$-th power. Let $M$ be a commutative group equipped with a $W(p,k)$-module structure which is free and finitely generated over $W(p,k)$, and let $U \colon M \to M$ be a homomorphism of additive groups which is semilinear for the Frobenius, that is, $U(w \cdot x) = \mathrm{frobenius}(w) \cdot U(x)$ for all $w \in W(p,k)$ and all $x \in M$, and which is bijective as a map of sets. Then there exists a $W(p,k)$-basis of $M$ indexed by $\mathrm{Fin}\,n$, where $n = \mathrm{finrank}_{W(p,k)} M$, all of whose members are fixed by $U$: $U(b_i) = b_i$ for every $i$. (Equivalently, each $A \in \mathrm{GL}_n(W(p,k))$ can be written as $A = P\,\sigma(P)^{-1}$ for some $P \in \mathrm{GL}_n(W(p,k))$.)
--
--   This is the statement that a unit-root $F$-crystal over the Witt vectors of an algebraically closed field of characteristic $p$ is constant, in the form used in Dieudonné-theoretic arguments; the corresponding statement over $k$ itself, for an injective $p$-semilinear endomorphism of a finite-dimensional $k$-vector space, is what the proof invokes. It is used in the classification of special formal $\mathcal{O}_D$-modules over an algebraically closed field, where at a critical index a bijective Frobenius-semilinear operator on a free $W(k)$-module of rank $2$ is trivialised by a basis of fixed vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddMonoidHom_exists_basis_apply_eq_self_of_map_smul_eq_frobenius_smul_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem AddMonoidHom.exists_basis_apply_eq_self_of_map_smul_eq_frobenius_smul_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (M : Type v) [AddCommGroup M] [Module (WittVector p k) M]
    [Module.Free (WittVector p k) M] [Module.Finite (WittVector p k) M]
    (U : M →+ M) (hU : ∀ (w : WittVector p k) (x : M), U (w • x) = WittVector.frobenius w • U x)
    (hbij : Function.Bijective U) :
    ∃ b : Module.Basis (Fin (Module.finrank (WittVector p k) M)) (WittVector p k) M,
      ∀ i, U (b i) = b i := by sorry
