-- Prove2me | Theorems.Thm_Bialgebra_nonempty_bialgEquiv_monoidAlgebra_of_basis_pow_of_comul_eq_tmul_self
-- name    : Bialgebra.nonempty_bialgEquiv_monoidAlgebra_of_basis_pow_of_comul_eq_tmul_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/3150ae29-a2f8-5e76-8418-f5e53857d146
-- title:
--   Bialgebra with basis of powers of a group-like element is R[ℤ/n]
-- statement:
--   Let $R$ be a commutative ring and $H$ a commutative ring carrying the structure of an $R$-bialgebra, let $n$ be a nonzero natural number, and let $x \in H$. Assume that $x$ is group-like, in the sense that the comultiplication of $H$ sends $x$ to $x \otimes_R x$ and the counit sends $x$ to $1$, that $x^n = 1$, and that there is an $R$-basis $b$ of $H$ indexed by $\mathrm{Fin}\ n$ with $b_i = x^{i}$ for every $i$, so that $1, x, \dots, x^{n-1}$ is a basis of $H$ as an $R$-module. The conclusion is that the type of $R$-bialgebra equivalences from $H$ to the monoid algebra $R[\,\mathrm{Multiplicative}(\mathbb{Z}/n\mathbb{Z})\,]$ is nonempty; that is, $H$ is isomorphic as an $R$-bialgebra to the group algebra over $R$ of the cyclic group of order $n$. The statement asserts existence of such an equivalence rather than producing a designated one.
--
--   This is the elementary structure statement identifying a commutative bialgebra spanned by the powers of a group-like element of order dividing $n$ with the group algebra of $\mathbb{Z}/n\mathbb{Z}$, equivalently the dual statement that the corresponding affine group scheme is the diagonalisable group $\mu_n$. It is used as the final identification step in [`HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_ne_two`](thm.html#HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_ne_two), within the classification of Oort–Tate type group schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Bialgebra_nonempty_bialgEquiv_monoidAlgebra_of_basis_pow_of_comul_eq_tmul_self.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u v

theorem Bialgebra.nonempty_bialgEquiv_monoidAlgebra_of_basis_pow_of_comul_eq_tmul_self
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [Bialgebra R H]
    (n : ℕ) [NeZero n] (x : H)
    (hΔ : Coalgebra.comul (R := R) x = x ⊗ₜ[R] x) (hε : Coalgebra.counit (R := R) x = 1)
    (hxn : x ^ n = 1)
    (b : Module.Basis (Fin n) R H) (hb : ∀ i : Fin n, b i = x ^ (i : ℕ)) :
    Nonempty (H ≃ₐc[R] MonoidAlgebra R (Multiplicative (ZMod n))) := by sorry
