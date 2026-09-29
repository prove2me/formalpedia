-- Prove2me | Theorems.Thm_CartierDual_exists_bialgEquiv_baseChange_forall_pairing_symm_tmul
-- name    : CartierDual.exists_bialgEquiv_baseChange_forall_pairing_symm_tmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/9f6df004-927d-53fc-9959-0a0a3cea8fe7
-- title:
--   Cartier duality commutes with base change
-- statement:
--   Let $R$ and $S$ be commutative rings with $S$ an $R$-algebra, and let $A$ be a commutative ring carrying an $R$-bialgebra structure which is finite and free as an $R$-module. The assertion is the existence of an isomorphism $e$ of $S$-bialgebras
--   $$e : \mathrm{CartierDual}_S\bigl(S \otimes_R A\bigr) \;\xrightarrow{\ \sim\ }\; S \otimes_R \mathrm{CartierDual}_R(A),$$
--   where [`CartierDual R A`](def/HopfAlgebra_CartierDual.html#L12) is by definition the $R$-linear dual $\mathrm{Hom}_R(A,R)$ equipped with its bialgebra structure, the source is the corresponding construction for the base-changed $S$-bialgebra $S \otimes_R A$, and the target carries the $S$-bialgebra structure obtained from $\mathrm{CartierDual}_R(A)$ by base change along $R \to S$. Moreover $e$ is pinned down on elementary tensors by the evaluation pairing: for all $s, t \in S$, every $\varphi \in \mathrm{CartierDual}_R(A)$ and every $a \in A$, the $S$-linear functional $e^{-1}(s \otimes \varphi)$ on $S \otimes_R A$ sends $t \otimes a$ to $s\,t\cdot \iota(\varphi(a))$, where $\iota =$ `algebraMap R S` and [`CartierDual.pairing`](def/HopfAlgebra_CartierDualMap.html#L18) is evaluation of a dual element on an algebra element. No uniqueness of $e$ is claimed.
--
--   This is the base-change compatibility of Cartier duality, $(G_S)^D \cong (G^D)_S$ for a finite flat commutative group scheme $G = \operatorname{Spec} A$ over $R$, in its bialgebra formulation, with the comparison isomorphism normalised by the evaluation pairing. It is used in the study of finite flat group schemes over local rings — for instance in the étale quotient and residue-field reduction statements for Cartier duals, and in the Dieudonné-module computation comparing the kernel of Frobenius with the cokernel of Verschiebung.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_exists_bialgEquiv_baseChange_forall_pairing_symm_tmul.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

universe u v w

open scoped TensorProduct in

theorem CartierDual.exists_bialgEquiv_baseChange_forall_pairing_symm_tmul
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (A : Type w) [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A] :
    ∃ e : CartierDual S (S ⊗[R] A) ≃ₐc[S] S ⊗[R] CartierDual R A,
      ∀ (s t : S) (φ : CartierDual R A) (a : A),
        CartierDual.pairing S (S ⊗[R] A) (e.symm (s ⊗ₜ[R] φ)) (t ⊗ₜ[R] a) =
          s * t * algebraMap R S (CartierDual.pairing R A φ a) := by sorry
