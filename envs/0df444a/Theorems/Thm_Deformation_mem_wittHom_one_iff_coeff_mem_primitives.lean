-- Prove2me | Theorems.Thm_Deformation_mem_wittHom_one_iff_coeff_mem_primitives
-- name    : Deformation.mem_wittHom_one_iff_coeff_mem_primitives
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/911c288d-347a-5a1f-8a07-b033276fc03d
-- title:
--   Length-one Witt homomorphisms are the primitive elements
-- statement:
--   Let $k$ be a field of characteristic $p$, where $p$ is a prime, and let $A$ be a commutative ring carrying a Hopf algebra structure over $k$. Let $x$ be a truncated Witt vector of length $1$ with entries in $A$. The assertion is an equivalence between two conditions on $x$. On one side, $x$ belongs to [`Deformation.wittHom k p 1 A`](def/Dieudonne_WittVectorHom.html#L246), that is, to the additive subgroup of $W_1(A)$ consisting of those vectors $y$ with $$W_1(\Delta)(y) = W_1(\iota_1)(y) + W_1(\iota_2)(y)$$ in $W_1(A \otimes_k A)$, where $\Delta$ is the comultiplication of $A$ viewed as a ring homomorphism $A \to A \otimes_k A$, $\iota_1, \iota_2$ are the two inclusions $a \mapsto a \otimes 1$ and $a \mapsto 1 \otimes a$, and $W_1(-)$ denotes the functorial action on truncated Witt vectors of length $1$. On the other side, the single coefficient $x_0 =$ `x.coeff 0` lies in [`primitives k A`](def/Dieudonne_ModpRealization.html#L16), the $k$-submodule of $A$ defined as the kernel of the $k$-linear map $a \mapsto \Delta a - a \otimes 1 - 1 \otimes a$.
--
--   This identifies the first stage $\operatorname{Hom}(G, W_1)$ of the Dieudonné module $\varinjlim_n \operatorname{Hom}(G, W_n)$ of the commutative affine group scheme $G$ with Hopf coordinate ring $A$ as the space of primitive elements of $A$. It is used in the mod-$p$ Dieudonné theory of the project, in particular in the results on the kernel of the Verschiebung and on the rank and order computations for Cartier duals of finite local group schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_mem_wittHom_one_iff_coeff_mem_primitives.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_Dieudonne_WittVectorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.mem_wittHom_one_iff_coeff_mem_primitives
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [HopfAlgebra k A] (x : TruncatedWittVector p 1 A) :
    x ∈ Deformation.wittHom k p 1 A ↔ x.coeff 0 ∈ primitives k A := by sorry
