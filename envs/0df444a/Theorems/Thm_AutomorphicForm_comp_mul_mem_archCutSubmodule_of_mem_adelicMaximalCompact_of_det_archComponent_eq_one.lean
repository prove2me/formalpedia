-- Prove2me | Theorems.Thm_AutomorphicForm_comp_mul_mem_archCutSubmodule_of_mem_adelicMaximalCompact_of_det_archComponent_eq_one
-- name    : AutomorphicForm.comp_mul_mem_archCutSubmodule_of_mem_adelicMaximalCompact_of_det_archComponent_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/192e8b7b-84cf-5a57-869e-0da333224058
-- title:
--   Stability of the archimedean cut under determinant-one compact translation
-- statement:
--   Let $F$ be a number field and let `tys` be an archimedean type family for $F$: data consisting of a cardinality function $w \mapsto \mathrm{card}(w)$ on the infinite places of $F$ and, for each infinite place $w$ and each index $i < \mathrm{card}(w)$, an archimedean type `tys.rep w i` at $w$, namely a natural number $n$ together with a representation $\rho$ of the group `rowIsometrySubgroup₀ w.Completion` on $\mathrm{Fin}\,n \to \mathbb{C}$. Write $\mathrm{GL}_2(\mathbb{A}_F)$ for `AdelicGL2 (𝓞 F) F`, the general linear group of $2 \times 2$ matrices over the adele ring. The archimedean cut `archCutSubmodule F tys` is the $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ given by the infimum over all infinite places $w$ of the supremum over $i < \mathrm{card}(w)$ of the type submodules `typeSubmodule (rowIsometryInclAt₀ F w) ρ` attached to the representation $\rho$ of `tys.rep w i` along the homomorphism `rowIsometryInclAt₀ F w` from the determinant-one row-isometry group at $w$ into $\mathrm{GL}_2(\mathbb{A}_F)$. Assume $f : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ lies in this cut, and let $k \in \mathrm{GL}_2(\mathbb{A}_F)$ lie in `adelicMaximalCompact F`, i.e. its finite part `glFin (𝓞 F) F k` lies in `finiteIntegralGL2 (𝓞 F) F` (the level-zero subgroup at the unit ideal) and, at every infinite place $w$, its archimedean component `archComponent F w (glArch (𝓞 F) F k)` is a row isometry: the norm of its determinant is $1$ and $(x,y) \mapsto (x k_{00} + y k_{10},\, x k_{01} + y k_{11})$ preserves $\lVert x \rVert^2 + \lVert y \rVert^2$ for all $x, y$ in the completion $F_w$. Assume further that at every infinite place $w$ the determinant of that archimedean component equals exactly $1$. Then the right translate $x \mapsto f(xk)$ again lies in `archCutSubmodule F tys`.
--
--   This is the statement that the archimedean type cut of a space of functions on $\mathrm{GL}_2(\mathbb{A}_F)$ is stable under right translation by the determinant-one part of the standard maximal compact subgroup, the product over the infinite places of the determinant-one row-isometry groups times $\mathrm{GL}_2(\widehat{\mathcal{O}})$. It is used in the construction of finite-dimensional bi-invariant pieces of the cut and in assembling cut conditions for induced sections at principal level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_comp_mul_mem_archCutSubmodule_of_mem_adelicMaximalCompact_of_det_archComponent_eq_one.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

theorem AutomorphicForm.comp_mul_mem_archCutSubmodule_of_mem_adelicMaximalCompact_of_det_archComponent_eq_one
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : f ∈ archCutSubmodule F tys)
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ adelicMaximalCompact F)
    (hdet : ∀ w : InfinitePlace F,
      ((archComponent F w (glArch (𝓞 F) F k) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det = 1) :
    (fun x => f (x * k)) ∈ archCutSubmodule F tys := by sorry
