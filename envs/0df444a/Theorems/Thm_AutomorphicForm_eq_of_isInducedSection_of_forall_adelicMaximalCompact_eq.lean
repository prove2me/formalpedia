-- Prove2me | Theorems.Thm_AutomorphicForm_eq_of_isInducedSection_of_forall_adelicMaximalCompact_eq
-- name    : AutomorphicForm.eq_of_isInducedSection_of_forall_adelicMaximalCompact_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/27afb4ef-3a64-5b4c-80f7-9c11a4bd468e
-- title:
--   Induced sections agree when they agree on the maximal compact
-- statement:
--   Let $K$ be a number field, and write $\mathrm{GL}_2(\mathbb{A}_K)$ for `AdelicGL2 (𝓞 K) K`, the general linear group of $2\times 2$ matrices over the adele ring of $K$. Let $\chi_1,\chi_2\colon \mathbb{A}_K^\times \to \mathbb{C}^\times$ be group homomorphisms and let $\varphi_1,\varphi_2\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be functions, each assumed to satisfy `IsInducedSection`: for every $b$ in `adelicBorel`, the subgroup of matrices whose $(1,0)$ entry vanishes, and every $g$, one has $\varphi_i(bg)=\chi_1(b_{00})\,\chi_2(b_{11})\,\varphi_i(g)$, where $b_{00}$ and $b_{11}$ are the diagonal entries of $b$, viewed as units of $\mathbb{A}_K$ via `borelDiagFst` and `borelDiagSnd`. Assume further that $\varphi_1$ and $\varphi_2$ agree at every element $k$ of the subgroup `adelicMaximalCompact K`, that is, at every $k$ whose finite part `glFin` lies in `finiteIntegralGL2` and whose component at each infinite place $w$, obtained from the archimedean part `glArch` by `archComponent`, satisfies `IsRowIsometry`: its determinant has absolute value $1$ and the map $(x,y)\mapsto (xk_{00}+yk_{10},\,xk_{01}+yk_{11})$ on $w$-completions preserves $\|x\|^2+\|y\|^2$. The conclusion is that $\varphi_1=\varphi_2$ as functions on $\mathrm{GL}_2(\mathbb{A}_K)$.
--
--   This is the standard uniqueness statement for sections of an induced representation $I(\chi_1,\chi_2)$ of $\mathrm{GL}_2(\mathbb{A}_K)$: such a section is determined by its restriction to the maximal compact subgroup. It is used in the analytic part of the development to upgrade identities between induced sections verified on the maximal compact subgroup, such as expansions in an orthonormal family or convolution identities, to identities on the whole group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_of_isInducedSection_of_forall_adelicMaximalCompact_eq.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.eq_of_isInducedSection_of_forall_adelicMaximalCompact_eq
    (K : Type) [Field K] [NumberField K]
    (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (φ₁ φ₂ : AdelicGL2 (𝓞 K) K → ℂ)
    (h₁ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ₁) (h₂ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ₂)
    (h : ∀ k : adelicMaximalCompact K, φ₁ (k : AdelicGL2 (𝓞 K) K) = φ₂ (k : AdelicGL2 (𝓞 K) K)) :
    φ₁ = φ₂ := by sorry
