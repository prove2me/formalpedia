-- Prove2me | Theorems.Thm_AutomorphicForm_exists_eq_diagUnits2_of_normString_eq_toTensorGL_diagUnits2
-- name    : AutomorphicForm.exists_eq_diagUnits2_of_normString_eq_toTensorGL_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/5453926a-883f-56db-88ee-4074d2fa671d
-- title:
--   Diagonality of lifts with regular split diagonal norm string
-- statement:
--   Let $K$ and $L$ be fields with $L$ a finite Galois extension of $K$, let $\sigma$ be a $K$-algebra automorphism of $L$, and let $A$ be a commutative $K$-algebra. Let $a,b \in A^\times$ be such that $a-b$ is a unit of $A$, and let $\delta \in \mathrm{GL}_2(L \otimes_K A)$. Write $\mathrm{diagUnits2}\,x\,y$ for the element of $\mathrm{GL}_2$ given by the matrix $!![x,0;0,y]$ together with the inverse $!![x^{-1},0;0,y^{-1}]$, for units $x,y$ of the base ring; write [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) for the group homomorphism $\mathrm{GL}_2(A) \to \mathrm{GL}_2(L\otimes_K A)$ induced entrywise by $x \mapsto 1 \otimes x$; and write [`AutomorphicForm.normString`](def/AutomorphicForm_TwistedOrbital.html#L205) for the product $\prod_{i=0}^{[L:K]-1} \sigma^{i}(\delta)$, taken in the listed order over $i \in \{0,\dots,[L:K]-1\}$, where $\sigma$ acts on $\mathrm{GL}_2(L\otimes_K A)$ entrywise through the ring endomorphism [`AutomorphicForm.sigmaTensor K L A σ`](def/AutomorphicForm_TwistedOrbital.html#L199) of $L \otimes_K A$, which sends $l \otimes x$ to $\sigma(l) \otimes x$. Assume that this norm string of $\delta$ equals, as an element of $\mathrm{GL}_2(L\otimes_K A)$ and not merely up to conjugacy, the image of $\mathrm{diagUnits2}\,a\,b$ under [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71). Then there exist units $\alpha, \beta$ of $L \otimes_K A$ with $\delta = \mathrm{diagUnits2}\,\alpha\,\beta$.
--
--   This is the standard rigidity statement for $\sigma$-conjugacy in base change for $\mathrm{GL}(2)$: a lift whose norm is a regular split diagonal element (regularity being encoded by the invertibility of $a-b$) is itself diagonal. It is used in the computation of local and archimedean twisted weighted orbital integrals at split diagonal elements, where arbitrary lifts $\delta$ with prescribed norm must be pinned down to the diagonal torus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_eq_diagUnits2_of_normString_eq_toTensorGL_diagUnits2.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct in

theorem AutomorphicForm.exists_eq_diagUnits2_of_normString_eq_toTensorGL_diagUnits2
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (A : Type) [CommRing A] [Algebra K A]
    (a b : Aˣ) (hab : IsUnit ((a : A) - (b : A)))
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.normString K L A σ δ = AutomorphicForm.toTensorGL K L A (diagUnits2 a b)) :
    ∃ α β : (L ⊗[K] A)ˣ, δ = diagUnits2 α β := by sorry
