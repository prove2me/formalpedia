-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
-- name    : Deformation.DieudonneModule.exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/2100715f-d685-5255-b7bb-977f4900e6a1
-- title:
--   Order of the Dieudonné module of a unipotent group scheme
-- statement:
--   Let $k$ be a finite field of characteristic $p$, with $p$ prime, and let $B$ be a commutative ring equipped with a Hopf algebra structure over $k$ whose comultiplication is cocommutative and which is finite as a $k$-module; thus $\operatorname{Spec} B$ is a finite commutative group scheme over $k$. Assume that the Cartier dual [`CartierDual k B`](def/HopfAlgebra_CartierDual.html#L12), namely the $k$-linear dual $\operatorname{Hom}_k(B,k)$ with the ring structure dual to the Hopf structure of $B$, is a local ring. The assertion is that there exists a natural number $L$ such that simultaneously $\dim_k B = p^L$ and the Dieudonné module $\mathtt{Deformation.DieudonneModule}\ k\ p\ B$ has exactly $(\#k)^L$ elements, the cardinality being taken in the sense of `Nat.card` (so the equality in particular forces this module to be finite). Here the Dieudonné module is the direct limit, in additive commutative groups, of the subgroups $\mathtt{wittHom}\ k\ p\ n\ B \subseteq \mathbb{W}_n(B)$ of truncated Witt vectors $x$ of length $n$ satisfying $\mathbb{W}_n(\Delta)(x) = \mathbb{W}_n(\iota_1)(x) + \mathbb{W}_n(\iota_2)(x)$, where $\Delta$ is the comultiplication and $\iota_1,\iota_2 : B \to B \otimes_k B$ the two inclusions, the transition maps being induced by the shift maps $\mathbb{W}_n \to \mathbb{W}_m$ for $n \le m$.
--
--   This is the order formula for the Dieudonné module of a unipotent finite commutative group scheme over a finite field: such a group scheme has order a power $p^L$ of $p$, and its Dieudonné module has cardinality $(\#k)^L$, i.e. length $L$ over the Witt vectors of $k$. It is used in the construction of Dieudonné data and $p$-divisible towers from Dieudonné modules, and in the comparison of a group scheme with the points of its Dieudonné module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.DieudonneModule.exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
    (k : Type u) [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (B : Type v) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B]
    (hB : IsLocalRing (CartierDual k B)) :
    ∃ L : ℕ, Module.finrank k B = p ^ L ∧
      Nat.card (Deformation.DieudonneModule k p B) = Nat.card k ^ L := by sorry
