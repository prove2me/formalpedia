-- Prove2me | Theorems.Thm_AutomorphicForm_eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero
-- name    : AutomorphicForm.eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/42f05090-a236-594a-8445-615e66e126c8
-- title:
--   Vanishing on a set covering modulo GL₂(F) and the centre
-- statement:
--   Let $F$ be a number field, and write $\mathrm{GL}_2(\mathbb{A}_F)$ for the group `AdelicGL2 (𝓞 F) F` of invertible $2\times 2$ matrices over the adele ring of $F$. Let $\xi$ be a group homomorphism from the full subgroup $\top$ of $(\mathbb{A}_F)^\times$ to $\mathbb{C}^\times$, and let $\varphi\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a function satisfying `IsLsXiFunction (𝓞 F) F ⊤ ξ φ`, that is: $\varphi(\gamma g)=\varphi(g)$ for every $\gamma\in \mathrm{GL}_2(F)$, embedded adelically by `globalPoints`, and every $g$; and $\varphi(zg)=\xi(z)\varphi(g)$ for every idele $z$, viewed as the central scalar matrix `centralScalar (𝓞 F) F z`, and every $g$. Let $W\subseteq \mathrm{GL}_2(\mathbb{A}_F)$ satisfy `CoversModCentre F W`, i.e. for each $g$ there exist $\gamma\in \mathrm{GL}_2(F)$ and $z\in(\mathbb{A}_F)^\times$ with $\gamma g z\in W$ (the image of $\gamma$ under `globalPoints` on the left, the central scalar attached to $z$ on the right). If $\varphi$ vanishes at every point of $W$, then $\varphi$ is the zero function.
--
--   The statement records the elementary fact that an automorphic-type function with central character is determined by its restriction to any set covering $\mathrm{GL}_2(\mathbb{A}_F)$ modulo the global points and the centre; no continuity, measurability, growth or cuspidality condition enters. It is used as the injectivity step for restriction to a Siegel-type window, and is cited by [`AutomorphicForm.eq_zero_of_isCuspAutomorphicFnAt_productionPinsOf_of_coversModCentre_of_forall_mem_eq_zero`](thm.html#AutomorphicForm.eq_zero_of_isCuspAutomorphicFnAt_productionPinsOf_of_coversModCentre_of_forall_mem_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_SiegelCovering

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm AutomorphicForm.SiegelCovering

theorem AutomorphicForm.eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero
    (F : Type) [Field F] [NumberField F]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ)
    (W : Set (AdelicGL2 (𝓞 F) F)) (hcov : CoversModCentre F W)
    (h0 : ∀ x ∈ W, φ x = 0) : φ = 0 := by sorry
