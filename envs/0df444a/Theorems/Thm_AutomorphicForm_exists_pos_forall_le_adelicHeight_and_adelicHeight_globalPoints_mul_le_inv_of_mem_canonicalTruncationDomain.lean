-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
-- name    : AutomorphicForm.exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/7a6795c0-5553-5f27-ba12-f8457759f2d7
-- title:
--   Height floor on the canonical truncation domain
-- statement:
--   Let $F$ be a number field, and let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$. Write $H(g)=\mathrm{adelicHeight}\,F\,g$ for the adelic height of $g\in GL_2(\mathbb{A}_F)$, defined as the product of the archimedean factor $\prod_{v\mid\infty}\mathrm{localHeight}(g_v)^{\,\mathrm{mult}(v)}$ over the infinite places, applied to the archimedean component $\mathrm{glArch}$ of $g$, with the finitary product $\prod^{f}_{v}\mathrm{finLocalHeight}(g_v)$ over the height-one primes $v$ of $\mathcal{O}_F$, applied to the finite component $\mathrm{glFin}$ of $g$. Let $\Phi_0=\mathrm{canonicalTruncationDomain}\,F\,\alpha\,\beta$ be the domain component of the canonically chosen truncation datum for $(F,\alpha,\beta)$, that is, of a classically chosen datum satisfying `IsTruncationDatum` if one exists, and $\varnothing$ otherwise. Then there exists a real $h_0>0$ such that: first, $h_0\le H(g)$ for every $g\in\Phi_0$; and second, for every $g\in\Phi_0$ and every $\gamma\in GL_2(F)$ whose matrix entry in position $(1,0)$ (the lower-left entry) is non-zero, $H(\mathrm{globalPoints}(\gamma)\cdot g)\le h_0^{-1}$, where $\mathrm{globalPoints}$ is the entrywise map $GL_2(F)\to GL_2(\mathbb{A}_F)$ induced by $F\to\mathbb{A}_F$.
--
--   This is the reduction-theoretic comparison point between the two truncation operators used for $GL_2$ over a number field: a uniform positive lower bound for the adelic height on the truncation domain of the determinant slab $\alpha\le\|\det g\|\le\beta$, together with the resulting upper bound $h_0^{-1}$ for the heights of translates by rational elements outside the Borel subgroup. It is cited in the analytic continuation and integrability arguments for windowed automorphic forms, where it lets a single truncation parameter $T\ge h_0^{-1}$ be chosen so that the one-cusp truncation on the domain agrees with the truncation summed over all rational translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain.lean

import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    ∃ h₀ : ℝ, 0 < h₀ ∧
      (∀ g ∈ AutomorphicForm.canonicalTruncationDomain F α β,
        h₀ ≤ NumberField.AdelicHeight.adelicHeight F g) ∧
      (∀ g ∈ AutomorphicForm.canonicalTruncationDomain F α β, ∀ γ : GL (Fin 2) F,
        (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 →
          NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.globalPoints (𝓞 F) F γ * g) ≤ h₀⁻¹) := by sorry
