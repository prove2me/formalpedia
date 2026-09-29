-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous
-- name    : AutomorphicForm.exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/e503125b-929e-5ba8-b9a8-d13b6ab3c02b
-- title:
--   Local finite type on K for continuous families on adelic GL₂
-- statement:
--   Let $F$ be a number field and let $\varphi : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a family of complex-valued functions on the adelic general linear group $\mathrm{GL}_2$ over the adele ring of $(\mathcal{O}_F, F)$, subject to three hypotheses: for each $s$ the function $\varphi_s$ is archimedean $K$-finite, meaning that for every infinite place $w$ of $F$ the predicate `RightTranslatesSpanFinite` holds for the subgroup `archRowIsometrySubgroup F w` and $\varphi_s$ (finiteness of the span of the right translates of $\varphi_s$ under that subgroup); for each $s$ the function $\varphi_s$, regarded as a vector of `RightTranslationFn` with its right-translation action, is a smooth vector for the kernel of `glArch`, i.e. its stabiliser in that finite-adelic subgroup is open; and the map $(s,g) \mapsto \varphi_s(g)$ is continuous on $\mathbb{C} \times \mathrm{GL}_2(\mathbb{A}_F)$. The conclusion is that there exist a nonempty open set $U \subseteq \mathbb{C}$, a natural number $n$ and parameters $\sigma : \mathrm{Fin}\, n \to \mathbb{C}$ such that for every $s \in U$ there are coefficients $c : \mathrm{Fin}\, n \to \mathbb{C}$, depending on $s$ only, with $\varphi_s(k) = \sum_i c_i\,\varphi_{\sigma_i}(k)$ for every $k \in \mathrm{GL}_2(\mathbb{A}_F)$ whose finite component `glFin k` lies in `finiteIntegralGL2` (the level-zero subgroup for the unit ideal, both $g$ and $g^{-1}$ being integral) and whose component at each infinite place $w$, obtained from `glArch k` by `archComponent F w`, satisfies `IsRowIsometry`: its determinant has norm $1$ and the pairing $(x,y) \mapsto (x k_{00} + y k_{10},\, x k_{01} + y k_{11})$ preserves the sum of squared norms.
--
--   This is the local finite-type property of a continuous family of automorphic-type functions on adelic $\mathrm{GL}_2$: on a nonempty open set of parameters the restrictions of the members of the family to the maximal compact subgroup all lie in the span of finitely many fixed members. It is invoked by [`AutomorphicForm.exists_flat_isInducedSection_sum_eq_of_differentiable_family`](thm.html#AutomorphicForm.exists_flat_isInducedSection_sum_eq_of_differentiable_family), where a differentiable family of adelic sections is replaced by a finite linear combination of specialisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous
    (F : Type) [Field F] [NumberField F]
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (_hφK : ∀ s, IsArchKFinite F (φ s))
    (_hφf : ∀ s, IsKfSmooth F (φ s))
    (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2)) :
    ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧
      ∃ (n : ℕ) (σ : Fin n → ℂ), ∀ s ∈ U, ∃ c : Fin n → ℂ, ∀ k : AdelicGL2 (𝓞 F) F,
        glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        φ s k = ∑ i, c i * φ (σ i) k := by sorry
