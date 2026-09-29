-- Prove2me | Theorems.Thm_AutomorphicForm_psiLoc_eq_psiLocal_or_eq_inv_of_isGlobalAddChar_of_addCharLevel_eq_zero
-- name    : AutomorphicForm.psiLoc_eq_psiLocal_or_eq_inv_of_isGlobalAddChar_of_addCharLevel_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/0e0a1c77-8233-54b3-b85b-a4bdd1b03a33
-- title:
--   Level-zero global additive characters of A_ℚ are locally ψᵥ^{± 1}
-- statement:
--   Let $\psi$ be an additive character of the adele ring of $\mathbb Q$ with values in $\mathbb C^\times$ which is global in the sense of the project's structure `IsGlobalAddChar`: it is trivial on the image of $\mathbb Q$ under the diagonal embedding, it is continuous, and it is not the trivial character. For a height-one prime $v$ of $\mathcal O_{\mathbb Q}$, $\mathtt{psiLoc}\,\psi\,v$ denotes the character of the completion $\mathbb Q_v$ obtained by composing $\psi$ with the additive map `adeleSingleAt` that sends $y \in \mathbb Q_v$ to the adele with $v$-component $y$, all other finite components $0$, and archimedean part $0$; similarly `psiLocal ℚ v` is the composition of the standard adelic character `stdAddChar ℚ` (the character attached to the adelic trace datum of $\mathbb Q$) with the same map. Assume that for every height-one prime $v$ the quantity `addCharLevel (psiLoc ψ v)`, namely the supremum of those $n \in \mathbb Z$ for which $\psi_v$ is trivial on $\{x : |x|_v \le q^{-n}\}$ (written with `WithZero.exp`), is $0$. Then for the given $v$ one has $\mathtt{psiLoc}\,\psi\,v = (\mathtt{psiLocal ℚ } v)^{-1}$ or $\mathtt{psiLoc}\,\psi\,v = \mathtt{psiLocal ℚ } v$.
--
--   This is the rigidity statement, standard in Tate's local–global theory of additive characters, that an unramified-at-every-finite-place global character of $\mathbb A_{\mathbb Q}$ differs from the standard one only by the sign $\pm 1$, so that its local components coincide with the standard local characters up to inversion. It is used in the cubic-induction part of the Langlands–Tunnell argument, where local zeta integrals and root numbers must be computed against the standard local character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_psiLoc_eq_psiLocal_or_eq_inv_of_isGlobalAddChar_of_addCharLevel_eq_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction

theorem AutomorphicForm.psiLoc_eq_psiLocal_or_eq_inv_of_isGlobalAddChar_of_addCharLevel_eq_zero
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    psiLoc ψ v = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ ∨
      psiLoc ψ v = NumberField.StandardAddChar.psiLocal ℚ v := by sorry
