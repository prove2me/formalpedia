-- Prove2me | Theorems.Thm_AutomorphicForm_eq_stdAddChar_of_isGlobalAddChar_of_apply_infinitePlace_eq_exp
-- name    : AutomorphicForm.eq_stdAddChar_of_isGlobalAddChar_of_apply_infinitePlace_eq_exp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/c38595b7-6e0a-5dfe-92f9-4a349c1ecc7c
-- title:
--   Global additive character with e^{2π i t} at a real place is standard
-- statement:
--   Let $F$ be a number field and let $\psi$ be an additive character of the adele ring $\mathbb{A}_F$ of $F$ with values in $\mathbb{C}$. Assume $\psi$ satisfies `IsGlobalAddChar F`, that is: $\psi$ kills the principal adeles, $\psi(\iota(\alpha)) = 1$ for every $\alpha \in F$, where $\iota$ is the structure map $F \to \mathbb{A}_F$; $\psi$ is continuous; and $\psi \neq 1$. Let $w$ be an infinite place of $F$ with `w.IsReal`. Assume further that for every infinite adele $x$ in the archimedean part $\prod_{w'} F_{w'}$ whose components vanish at all infinite places $w' \neq w$, the value of $\psi$ at the adele $(x, 0)$ with zero finite part is $\exp(2\pi i\, \sigma_w(x_w))$, where $\sigma_w$ is the embedding `extensionEmbedding w` of the completion $F_w$ into $\mathbb{C}$. The conclusion is that $\psi$ equals the standard additive character [`NumberField.StandardAddChar.stdAddChar F`](def/NumberField_AdelicTraceFin.html#L198) of $\mathbb{A}_F$, namely the character obtained from the standard character of $\mathbb{A}_{\mathbb{Q}}$ by composing with the adelic trace homomorphism attached to $F$.
--
--   This is the uniqueness half of the description of characters of the adele class group $\mathbb{A}_F/F$ (Tate's thesis): the group of such characters is a single orbit $\{\psi_F(a\,\cdot)\}_{a \in F^\times}$ under $F^\times$, so normalising the component at one real place to $t \mapsto e^{2\pi i t}$ pins down the standard character. It is used in the Langlands–Tunnell part of the development to identify the additive character implicit in Whittaker coefficients with the standard one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_stdAddChar_of_isGlobalAddChar_of_apply_infinitePlace_eq_exp.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.InfinitePlace.Completion

theorem AutomorphicForm.eq_stdAddChar_of_isGlobalAddChar_of_apply_infinitePlace_eq_exp
    (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (w : InfinitePlace F) (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing F, (∀ w' : InfinitePlace F, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 F) F) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w))) :
    ψ = NumberField.StandardAddChar.stdAddChar F := by sorry
