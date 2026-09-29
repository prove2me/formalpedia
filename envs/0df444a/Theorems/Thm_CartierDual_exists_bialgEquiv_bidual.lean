-- Prove2me | Theorems.Thm_CartierDual_exists_bialgEquiv_bidual
-- name    : CartierDual.exists_bialgEquiv_bidual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/ae7cd5e4-38e3-57ab-ab93-113fac1689ce
-- title:
--   Cartier biduality for finite free cocommutative bialgebras
-- statement:
--   Let $R$ be a commutative ring and let $A$ be a commutative ring carrying an $R$-bialgebra structure which is finite and free as an $R$-module and whose comultiplication is cocommutative (`Coalgebra.IsCocomm R A`). Write $\mathrm{CartierDual}\,R\,A$ for the Cartier dual of $A$, which as a type is the $R$-linear dual $\operatorname{Hom}_R(A,R)$ equipped with the bialgebra structure attached to it by the project (multiplication and unit coming from the comultiplication and counit of $A$, and dually). The assertion is that there exists an isomorphism of $R$-bialgebras $e \colon A \xrightarrow{\ \sim\ } \mathrm{CartierDual}\,R\,(\mathrm{CartierDual}\,R\,A)$ — that is, an $R$-algebra isomorphism compatible with counits and comultiplications — such that for every $a \in A$ and every $\varphi$ in the Cartier dual of $A$ one has $e(a)(\varphi) = \varphi(a)$; so the isomorphism is the evaluation map. The statement is existential: it asserts that the evaluation pairing is a bialgebra isomorphism, without naming a term for it.
--
--   This is Cartier biduality $G \cong (G^{\vee})^{\vee}$ for finite locally free commutative group schemes, expressed on coordinate rings. It is used thirteen times in the development, in particular in the analysis of finite flat Hopf algebras and their Galois representations and in the passage between a Hopf algebra and its Cartier dual.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_exists_bialgEquiv_bidual.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CartierDual.exists_bialgEquiv_bidual
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A] :
    ∃ e : A ≃ₐc[R] CartierDual R (CartierDual R A), ∀ (a : A) (φ : CartierDual R A), e a φ = φ a := by sorry
