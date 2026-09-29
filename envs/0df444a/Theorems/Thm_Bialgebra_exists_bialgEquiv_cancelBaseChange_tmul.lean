-- Prove2me | Theorems.Thm_Bialgebra_exists_bialgEquiv_cancelBaseChange_tmul
-- name    : Bialgebra.exists_bialgEquiv_cancelBaseChange_tmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/c6d35921-8b0c-55b4-a86c-382517c9f992
-- title:
--   Cancelling an intermediate base change of a bialgebra
-- statement:
--   Let $R$, $R'$ and $S$ be commutative rings forming a scalar tower: $R'$ is an $R$-algebra, $S$ is both an $R'$-algebra and an $R$-algebra, and the two actions of $R$ on $S$ agree (via `IsScalarTower R R' S`). Let $C$ be a commutative ring equipped with the structure of an $R$-bialgebra. Both $S \otimes_{R'} (R' \otimes_R C)$ and $S \otimes_R C$ carry their canonical $S$-bialgebra structures obtained by base change of $C$ (over $R'$ and over $R$ respectively, using Mathlib's bialgebra structure on a tensor product). The assertion is that there exists an equivalence of $S$-bialgebras $e : S \otimes_{R'} (R' \otimes_R C) \simeq S \otimes_R C$ — that is, an $S$-algebra isomorphism compatible with the counits and the comultiplications — such that for all $s \in S$, $r \in R'$ and $c \in C$ one has $e(s \otimes (r \otimes c)) = (r \cdot s) \otimes c$, where $r \cdot s$ denotes the $R'$-action on $S$. The statement is an existence statement pinned down by these values on pure tensors, rather than the construction of a named map.
--
--   This is the bialgebra refinement of the cancellation isomorphism $S \otimes_{R'} (R' \otimes_R C) \cong S \otimes_R C$ for an iterated base change; Mathlib supplies the underlying $S$-algebra isomorphism, and the content here is that counit and comultiplication are respected. It is used when a bialgebra over a base ring is compared with its reduction through an intermediate ring, in the passage to residue fields in the analysis of torus quotients on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Bialgebra_exists_bialgEquiv_cancelBaseChange_tmul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Bialgebra.exists_bialgEquiv_cancelBaseChange_tmul
    (R R' S : Type*) [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R' S] [Algebra R S]
    [IsScalarTower R R' S] (C : Type*) [CommRing C] [Bialgebra R C] :
    ∃ e : S ⊗[R'] (R' ⊗[R] C) ≃ₐc[S] S ⊗[R] C, ∀ (s : S) (r : R') (c : C), e (s ⊗ₜ (r ⊗ₜ c)) = (r • s) ⊗ₜ c := by sorry
