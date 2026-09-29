-- Prove2me | Theorems.Thm_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_prime
-- name    : AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/84a7b4f7-44c9-53f9-a82b-f8684498e75b
-- title:
--   Twisted centralizer of a diagonal element with regular split norm
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra whose degree $\ell = \operatorname{finrank}_K L$ is a prime number, and let $\sigma \colon L \to L$ be a $K$-algebra automorphism with $\sigma \neq 1$. Let $A$ be a further field that is a $K$-algebra; $\sigma$ acts on $L \otimes_K A$ through the first factor, inducing the endomorphism [`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202) of $\mathrm{GL}_2(L \otimes_K A)$ by entrywise application, and $\mathrm{GL}_2(A)$ maps into $\mathrm{GL}_2(L \otimes_K A)$ by [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71), the entrywise application of $x \mapsto 1 \otimes x$. Let $a, b \in A^\times$ with $a \neq b$, and let $\alpha, \beta \in (L \otimes_K A)^\times$; write $\mathrm{diag}(x,y)$ for the element `diagUnits2 x y` of a general linear group, the diagonal matrix with entries $x, y$ and inverse $\mathrm{diag}(x^{-1},y^{-1})$. Assume the norm string of $\delta = \mathrm{diag}(\alpha,\beta)$, namely the ordered product $\delta \cdot \sigma(\delta) \cdots \sigma^{\ell-1}(\delta)$ over $i \in \{0,\dots,\ell-1\}$ of the $i$-fold iterates of `sigmaGL` applied to $\delta$, equals the image of $\gamma = \mathrm{diag}(a,b)$ under `toTensorGL`. Then the $\sigma$-twisted centralizer of $\delta$, that is the subgroup $\{\, t \in \mathrm{GL}_2(L \otimes_K A) : t\,\delta\,\sigma(t)^{-1} = \delta \,\}$, is equal to the image under `toTensorGL` of the centralizer of $\{\gamma\}$ in $\mathrm{GL}_2(A)$.
--
--   This is the computation of the $\sigma$-twisted centralizer at a diagonal element whose norm is regular split, as used in the base-change comparison of twisted and ordinary orbital integrals; the cyclicity of $L/K$ and $\sigma$ generating its Galois group are supplied by [`AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one`](thm.html#AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one). It feeds the evaluation of twisted weighted orbital integrals against indicators of semilocal integral sets and the comparison of twisted and untwisted weighted terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_prime
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [Field A] [Algebra K A]
    (a b : Aˣ) (hab : a ≠ b) (α β : (L ⊗[K] A)ˣ)
    (hN : AutomorphicForm.normString K L A σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L A (diagUnits2 a b)) :
    AutomorphicForm.twistedCentralizer K L A σ (diagUnits2 α β) =
      (Subgroup.centralizer ({diagUnits2 a b} : Set (GL (Fin 2) A))).map (AutomorphicForm.toTensorGL K L A) := by sorry
