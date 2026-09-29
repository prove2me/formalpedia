-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual
-- name    : Deformation.DieudonneModule.exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/072bdf86-0734-5f85-af1d-a1aa50630ab5
-- title:
--   Unipotent Hopf algebras: order p^L and Dieudonné module bound
-- statement:
--   Let $k$ be a finite field of characteristic $p$, with $p$ prime, and let $B$ be a commutative ring carrying the structure of a Hopf algebra over $k$ whose comultiplication is cocommutative and which is finite as a $k$-module. Assume that the Cartier dual [`CartierDual k B`](def/HopfAlgebra_CartierDual.html#L12), i.e. the $k$-linear dual $\operatorname{Hom}_k(B,k)$ with its ring structure (convolution), is a local ring. Then there exists a natural number $L$ such that, first, $\dim_k B = p^L$, and second, the number of elements of the Dieudonné module [`Deformation.DieudonneModule k p B`](def/Dieudonne_WittHomColimit.html#L234) is at most $(\#k)^L$. Here the Dieudonné module is the direct limit, as an additive commutative group, of the groups [`Deformation.wittHom k p n B`](def/Dieudonne_WittVectorHom.html#L246) along the maps induced by the truncated Witt shift `TruncWitt.shiftLE`, where [`Deformation.wittHom k p n B`](def/Dieudonne_WittVectorHom.html#L246) is the additive subgroup of the truncated Witt vectors $W_n(B)$ consisting of those $x$ with $W_n(\Delta)(x) = W_n(\iota_1)(x) + W_n(\iota_2)(x)$, for $\Delta : B \to B \otimes_k B$ the comultiplication and $\iota_1, \iota_2 : B \to B \otimes_k B$ the two inclusions. Both assertions are about cardinalities computed by `Nat.card`, so the inequality is stated for the cardinality of the limit group.
--
--   This is the upper-bound half of the classical order formula for the Dieudonné module of a unipotent finite commutative group scheme $H = \operatorname{Spec} B$ over a finite field: the order of $H$ is a power $p^L$ of $p$, and $M(H) = \varinjlim_n \operatorname{Hom}(H, W_n)$ has at most $(\#k)^L$ elements (classically it has length exactly $L$ over $W(k)$). It is used by [`Deformation.DieudonneModule.exists_map_eq_of_isLocalRing_cartierDual`](thm.html#Deformation.DieudonneModule.exists_map_eq_of_isLocalRing_cartierDual).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.DieudonneModule.exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual
    (k : Type u) [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (B : Type v) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B]
    (hB : IsLocalRing (CartierDual k B)) :
    ∃ L : ℕ, Module.finrank k B = p ^ L ∧
      Nat.card (Deformation.DieudonneModule k p B) ≤ Nat.card k ^ L := by sorry
