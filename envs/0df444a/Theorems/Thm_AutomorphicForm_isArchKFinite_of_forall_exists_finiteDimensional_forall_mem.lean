-- Prove2me | Theorems.Thm_AutomorphicForm_isArchKFinite_of_forall_exists_finiteDimensional_forall_mem
-- name    : AutomorphicForm.isArchKFinite_of_forall_exists_finiteDimensional_forall_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/761b68c0-206e-5aae-8e70-6e4940a5a125
-- title:
--   Uniform finite-dimensional translate spaces give archimedean K-finiteness
-- statement:
--   Let $F$ be a number field, and let $\varphi$ be a complex-valued function on `AdelicGL2 (𝓞 F) F`, the general linear group $\mathrm{GL}_2$ over the adele ring of $F$. Assume that for every infinite place $w$ of $F$ there is a $\mathbb{C}$-submodule $W$ of the space of all functions from the subgroup `archRowIsometrySubgroup F w` to $\mathbb{C}$ — this subgroup being the image, under the composite $\mathrm{GL}_2(F_w) \to \mathrm{GL}_2(\mathbb{A}_F)$ of `adelicArchGLInclAt F w`, of the subgroup of those $k \in \mathrm{GL}_2(F_w)$ satisfying `IsRowIsometry` — such that $W$ is finite-dimensional over $\mathbb{C}$ and, for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$, the restricted right translate $k \mapsto \varphi(gk)$, viewed as a function on that subgroup, belongs to $W$. The conclusion is `IsArchKFinite F φ`: for every infinite place $w$, the predicate `RightTranslatesSpanFinite` holds for the subgroup `archRowIsometrySubgroup F w` and the function $\varphi$, that is, the right translates $x \mapsto \varphi(xk)$, for $k$ ranging over that subgroup, all lie in the $\mathbb{C}$-span of one finite family of functions on $\mathrm{GL}_2(\mathbb{A}_F)$.
--
--   This converts one formulation of archimedean $K$-finiteness into another: from a finite-dimensional space of functions on the archimedean row-isometry subgroup containing every restricted translate $k \mapsto \varphi(gk)$, indexed by $g$, to finiteness of the span of the global translates $x \mapsto \varphi(xk)$, indexed by $k$. It is used on the Eisenstein side of the argument, by the results on axis continuations of Weyl intertwining integrals and on pseudo-Eisenstein and cusp-basis inner product identities.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchKFinite_of_forall_exists_finiteDimensional_forall_mem.lean

import Definitions.Def_AutomorphicForm_ArchKFinite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.isArchKFinite_of_forall_exists_finiteDimensional_forall_mem
    (F : Type) [Field F] [NumberField F] (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (_hKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (g : AdelicGL2 (𝓞 F) F),
        (fun k : ↥(archRowIsometrySubgroup F w) => φ (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) :
    IsArchKFinite F φ := by sorry
