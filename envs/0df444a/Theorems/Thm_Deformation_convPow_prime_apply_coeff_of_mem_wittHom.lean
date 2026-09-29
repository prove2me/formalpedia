-- Prove2me | Theorems.Thm_Deformation_convPow_prime_apply_coeff_of_mem_wittHom
-- name    : Deformation.convPow_prime_apply_coeff_of_mem_wittHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/dfe6a355-c419-5539-80cc-9b5862da7b5e
-- title:
--   Convolution p-th powers shift Witt coordinates of a homomorphism
-- statement:
--   Let $p$ be a prime, let $k$ be a commutative ring of characteristic $p$, let $A$ be a commutative ring carrying a $k$-bialgebra structure, let $T$ be a commutative $k$-algebra, and let $\beta$ be an element of `WithConv (A →ₗ[k] T)`, that is a $k$-linear map $A \to T$ regarded as an element of the convolution algebra of such maps (with `ofConv` the passage back to the underlying linear map). Let $n$ be a natural number and let $x$ be a truncated Witt vector of length $n$ with coordinates in $A$, assumed to lie in the additive subgroup [`Deformation.wittHom k p n A`](def/Dieudonne_WittVectorHom.html#L246), i.e. to satisfy
--   $$W_n(\Delta)(x) = W_n(\iota_1)(x) + W_n(\iota_2)(x) \quad\text{in } W_n(A \otimes_k A),$$
--   where $\Delta$ is the comultiplication of $A$ viewed as a ring homomorphism $A \to A \otimes_k A$, and $\iota_1, \iota_2$ are the two inclusions $a \mapsto a \otimes 1$, $a \mapsto 1 \otimes a$, all three acting coordinatewise on truncated Witt vectors. The conclusion is the conjunction of two assertions: first, if $0 < n$ then the linear map underlying the $p$-th convolution power $\beta^{p}$ annihilates the $0$-th coordinate $x_0$; second, for every $i$ with $i + 1 < n$, the value of that map on the coordinate $x_{i+1}$ equals $(\beta(x_i))^{p}$.
--
--   This is the Verschiebung relation $x \circ V_G = V_W \circ x^{(p)}$ for a homomorphism $x$ from the monoid scheme $\operatorname{Spec} A$ to the group of Witt vectors of length $n$, written out after evaluation against a $k$-linear functional $\beta$, the $p$-th convolution power playing the role of the transpose of the Verschiebung of $\operatorname{Spec} A$. It is used in the Dieudonné-theoretic part of the deformation argument, for instance in the analysis of when the coordinates of such a homomorphism generate $A$ and in the reconstruction of Witt-vector homomorphisms from prescribed coordinates or truncations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_convPow_prime_apply_coeff_of_mem_wittHom.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem Deformation.convPow_prime_apply_coeff_of_mem_wittHom
    (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [Bialgebra k A]
    (T : Type w) [CommRing T] [Algebra k T] (β : WithConv (A →ₗ[k] T))
    {n : ℕ} {x : TruncatedWittVector p n A} (hx : x ∈ Deformation.wittHom k p n A) :
    (∀ h : 0 < n, (β ^ p).ofConv (x.coeff ⟨0, h⟩) = 0) ∧
    ∀ (i : ℕ) (hi : i + 1 < n),
      (β ^ p).ofConv (x.coeff ⟨i + 1, hi⟩) = (β.ofConv (x.coeff ⟨i, Nat.lt_of_succ_lt hi⟩)) ^ p := by sorry
