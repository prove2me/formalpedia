-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_map_surjective_of_surjective
-- name    : Deformation.DieudonneModule.map_surjective_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/34e4e453-1ce7-5108-bea0-28a7c0f0f357
-- title:
--   Surjectivity of M(π) for surjective π (right exactness)
-- statement:
--   Let $p$ be a prime and let $k$ be a field of characteristic $p$ that is perfect (a `PerfectRing` for the exponent $p$). Let $A$ be a commutative ring carrying a $k$-Hopf algebra structure whose comultiplication is cocommutative and which is finite-dimensional as a $k$-module, and let $B$ be a commutative ring carrying a $k$-bialgebra structure. Let $\pi : A \to B$ be a homomorphism of $k$-bialgebras (simultaneously a $k$-algebra and a $k$-coalgebra map) and assume $\pi$ is surjective as a function. Here, for each $n$, `wittHom k p n A` is the additive subgroup of the truncated Witt vectors $W_n(A)$ consisting of those $x$ with $W_n(\Delta)(x) = W_n(\iota_1)(x) + W_n(\iota_2)(x)$ in $W_n(A \otimes_k A)$, where $\Delta$ is the comultiplication and $\iota_1,\iota_2$ the two inclusions of $A$ into $A \otimes_k A$; `DieudonneModule k p A` is the direct limit of these groups along the maps induced by the iterated shift $(x_0,\dots,x_{n-1}) \mapsto (0,x_0,\dots,x_{n-1})$, and `DieudonneModule.map k p π` is the additive group homomorphism out of this limit induced, level by level, by $x \mapsto W_n(\pi)(x)$. The assertion is that `DieudonneModule.map k p π` is a surjective function.
--
--   This is the right exactness of the contravariant Dieudonné module functor $M(G) = \varinjlim_n \operatorname{Hom}(G, W_n)$ on finite commutative group schemes over a perfect field: a closed immersion $H = \operatorname{Spec} B \hookrightarrow G = \operatorname{Spec} A$, presented as a surjection of bialgebras, induces a surjection $M(G) \to M(H)$ of Dieudonné modules. It feeds the computation of the kernel of $M(\pi)$ and, through that, the analysis of torsion in group schemes attached to modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_map_surjective_of_surjective.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem Deformation.DieudonneModule.map_surjective_of_surjective
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    {A : Type v} [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    {B : Type w} [CommRing B] [Bialgebra k B]
    (π : A →ₐc[k] B) (hπ : Function.Surjective π) :
    Function.Surjective (Deformation.DieudonneModule.map k p π) := by sorry
