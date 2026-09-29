-- Prove2me | Theorems.Thm_AutomorphicForm_continuousOn_of_isInducedSection_of_continuousOn_maximalCompact
-- name    : AutomorphicForm.continuousOn_of_isInducedSection_of_continuousOn_maximalCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/fe8b7c4f-9e72-56b0-8802-409f985ae421
-- title:
--   Continuity of Borel-induced sections from the maximal compact
-- statement:
--   Let $F$ be a number field, $X$ a topological space and $U \subseteq X$ an open set. Let $\chi_1, \chi_2$ assign to each $x \in X$ a group homomorphism $(\mathbb{A}_F)^\times \to \mathbb{C}^\times$, where $\mathbb{A}_F$ is the adele ring `AdeleRing (𝓞 F) F`, and assume that the two functions $(x,y) \mapsto \chi_i(x)(y) \in \mathbb{C}$ are continuous on $U \times (\mathbb{A}_F)^\times$. Let $f : X \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be such that: for every $x \in U$ the function $f(x,\cdot)$ satisfies `IsInducedSection`, namely $f(x, bg) = \chi_1(x)(b_{00})\,\chi_2(x)(b_{11})\, f(x,g)$ for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ and every $b$ in `adelicBorel`, the subgroup of elements whose $(1,0)$ entry vanishes, with $b_{00}, b_{11}$ the units extracted by `borelDiagFst`, `borelDiagSnd`; and $(x,k) \mapsto f(x,k)$ is continuous on the product of $U$ with the set of $k \in \mathrm{GL}_2(\mathbb{A}_F)$ whose finite component `glFin` lies in `finiteIntegralGL2` and whose component at each infinite place $w$ of $F$, obtained via `glArch` followed by `archComponent F w`, satisfies `IsRowIsometry`, i.e. has determinant of norm $1$ and satisfies $\|xk_{00} + yk_{10}\|^2 + \|xk_{01} + yk_{11}\|^2 = \|x\|^2 + \|y\|^2$ for all scalars $x,y$. Then $(x,g) \mapsto f(x,g)$ is continuous on $U \times \mathrm{GL}_2(\mathbb{A}_F)$. The hypothesis that $U$ is open is part of the statement.
--
--   This is the continuity criterion for families of sections induced from the Borel subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$: joint continuity in the parameter and the group variable follows from joint continuity on the maximal compact subgroup alone, via the adelic Iwasawa decomposition supplied by [`AutomorphicForm.exists_mem_adelicBorel_mul_eq`](thm.html#AutomorphicForm.exists_mem_adelicBorel_mul_eq). It is used in the construction of parametrised families of induced sections and of their Weyl intertwining integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuousOn_of_isInducedSection_of_continuousOn_maximalCompact.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_RowIsometryInvariance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel Topology

theorem AutomorphicForm.continuousOn_of_isInducedSection_of_continuousOn_maximalCompact
    (F : Type) [Field F] [NumberField F]
    {X : Type*} [TopologicalSpace X] (U : Set X) (_hU : IsOpen U)
    (χ₁ χ₂ : X → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
    (_hχ₁ : ContinuousOn (fun p : X × (AdeleRing (𝓞 F) F)ˣ => ((χ₁ p.1 p.2 : ℂˣ) : ℂ)) (U ×ˢ Set.univ))
    (_hχ₂ : ContinuousOn (fun p : X × (AdeleRing (𝓞 F) F)ˣ => ((χ₂ p.1 p.2 : ℂˣ) : ℂ)) (U ×ˢ Set.univ))
    (f : X → AdelicGL2 (𝓞 F) F → ℂ)
    (_hf : ∀ x ∈ U, IsInducedSection (𝓞 F) F (χ₁ x) (χ₂ x) (f x))
    (_hfK : ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2)
      (U ×ˢ {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))})) :
    ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2) (U ×ˢ Set.univ) := by sorry
