-- Prove2me | Theorems.Thm_Deformation_wittHomShift_surjective_of_forall_convPow_eq_zero
-- name    : Deformation.wittHomShift_surjective_of_forall_convPow_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/d7360549-87d2-5853-8688-9012f2a81ad0
-- title:
--   Witt shift is surjective when β(1)=0 forces β^{p^n}=0
-- statement:
--   Let $k$ be a field of characteristic $p$ for a prime $p$, let $A$ be a commutative $k$-bialgebra, and let $n$ be a natural number. For a $k$-algebra $T$, write $\mathrm{WithConv}(A \to_{l} T)$ for the $k$-linear dual-type space $A \to_{l} T$ equipped with the convolution ring structure, with `ofConv` the underlying linear map and with powers taken for convolution. Assume the hypothesis $hV$: every $\beta \in \mathrm{WithConv}(A \to_{l} k)$ with $\beta(1) = 0$ satisfies $\beta^{p^n} = 0$ in the convolution ring. Let $m \ge n$. For each $j$, [`Deformation.wittHom k p j A`](def/Dieudonne_WittVectorHom.html#L246) is the additive subgroup of the truncated Witt vectors $W_j(A)$ of those $x$ with $W_j(\Delta)(x) = W_j(\iota_1)(x) + W_j(\iota_2)(x)$, where $\Delta \colon A \to A \otimes_k A$ is the comultiplication and $\iota_1, \iota_2$ are the two inclusions of $A$ into $A \otimes_k A$; and [`Deformation.wittHomShift k p m A`](def/Dieudonne_WittVectorHom.html#L446) is the additive homomorphism from `wittHom k p m A` to `wittHom k p (m+1) A` induced by the shift map $W_m(A) \to W_{m+1}(A)$ coming from Verschiebung (insert $0$ in coefficient $0$ and move the old coefficients up by one). The conclusion is that this map [`Deformation.wittHomShift k p m A`](def/Dieudonne_WittVectorHom.html#L446) is surjective.
--
--   In the Dieudonné theory of commutative group schemes over $k$, the subgroup `wittHom k p j A` is the group of homomorphisms of $\mathrm{Spec}\,A$ into the truncated Witt vectors $W_j$, and the shift maps are the transition maps whose colimit is the Dieudonné module; the statement is the assertion that for a group scheme whose Verschiebung is killed in $n$ steps (expressed dually through convolution powers of linear functionals annihilating $1$) every homomorphism into $W_{m+1}$ with $m \ge n$ has vanishing zeroth coordinate and so factors through $W_m$. It is used in the computation of the rank and cardinality statements for Dieudonné modules of group schemes with local Cartier dual, and in the corresponding surjectivity statement for the induced maps on Hopf algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_wittHomShift_surjective_of_forall_convPow_eq_zero.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.wittHomShift_surjective_of_forall_convPow_eq_zero
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [Bialgebra k A] (n : ℕ)
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ n = 0)
    (m : ℕ) (hm : n ≤ m) :
    Function.Surjective (Deformation.wittHomShift k p m A) := by sorry
