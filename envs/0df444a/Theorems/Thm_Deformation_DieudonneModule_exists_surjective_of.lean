-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_exists_surjective_of
-- name    : Deformation.DieudonneModule.exists_surjective_of
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/47b5a132-0ba3-50af-8ec1-d38a364f5b50
-- title:
--   Stabilisation of the Dieudonné module over a perfect field
-- statement:
--   Let $k$ be a field of characteristic $p$, for a prime $p$, which is perfect in the sense that the $p$-th power map on $k$ is bijective, and let $A$ be a commutative ring which is a Hopf algebra over $k$ whose underlying coalgebra is cocommutative and which is finite as a $k$-module. For each $n$, `Deformation.DieudonneModule.wittHom k p n A` is the additive subgroup of the truncated Witt vectors $W_n(A)$ consisting of those $x$ with $W_n(\Delta)(x) = W_n(\iota_1)(x) + W_n(\iota_2)(x)$, where $\Delta \colon A \to A \otimes_k A$ is the comultiplication and $\iota_1, \iota_2 \colon A \to A \otimes_k A$ are the two inclusions; that is, the group of primitive elements of $W_n(A)$, equivalently of group-scheme homomorphisms $\operatorname{Spec} A \to W_n$. These groups form a directed system along the maps induced by the length-shifting maps $W_n(A) \to W_m(A)$ for $n \le m$, and [`Deformation.DieudonneModule k p A`](def/Dieudonne_WittHomColimit.html#L234) is the colimit, with [`Deformation.DieudonneModule.of k p A N`](def/Dieudonne_WittHomColimit.html#L245) the canonical homomorphism from the $N$-th term. The assertion is that there exists an $N \in \mathbb{N}$ for which this canonical map is surjective.
--
--   This is the stabilisation statement for the Dieudonné module of a finite commutative group scheme over a perfect field of characteristic $p$, equivalent to the nilpotence of the Verschiebung on $M(G)$: the whole module is already reached at a finite level $\operatorname{Hom}(G, W_N)$. It underlies the subsequent computations of the $k$-dimension and cardinality attached to local Cartier duals and the comparison of Honda systems with Fontaine–Hodge data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_exists_surjective_of.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.DieudonneModule.exists_surjective_of
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A] :
    ∃ N : ℕ, Function.Surjective (Deformation.DieudonneModule.of k p A N) := by sorry
