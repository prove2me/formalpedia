-- Prove2me | Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
-- name    : AutomorphicForm.adelicKernelLocalFiniteness
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/90b3bea0-997a-557d-ba05-01bc5ef8e248
-- title:
--   Uniform discreteness of GL₂(F) in GL₂(A_F)
-- statement:
--   Let $F$ be a field which is a number field, with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`, and write $G(\mathbb{A}_F)$ for `AdelicGL2 (𝓞 F) F`, the general linear group $\mathrm{GL}_2$ over $\mathbb{A}_F$, carrying its usual topology as a group of units. Let $\iota =$ `globalPoints (𝓞 F) F` be the group homomorphism $\mathrm{GL}_2(F) \to G(\mathbb{A}_F)$ obtained by applying the structure map $F \to \mathbb{A}_F$ entrywise. The theorem asserts that the predicate [`AutomorphicForm.AdelicKernelLocalFiniteness F`](def/AutomorphicForm_AdelicKernel.html#L37) holds, i.e.: for every subset $C \subseteq G(\mathbb{A}_F)$ which is compact, and for all $x, y \in G(\mathbb{A}_F)$, the set
--   $$\{\gamma \in \mathrm{GL}_2(F) \;:\; x^{-1}\,\iota(\gamma)\,y \in C\}$$
--   is finite. Nothing is claimed here about the quotient $\mathrm{GL}_2(F)\backslash G(\mathbb{A}_F)$ or about fundamental domains; the conclusion is exactly the stated finiteness of the double-translate fibres of the rational points over compact sets.
--
--   This is the uniform discreteness of the rational points $\mathrm{GL}_2(F)$ inside the adelic group $\mathrm{GL}_2(\mathbb{A}_F)$, in the form needed to make the automorphic kernel $K_f(x,y) = \sum_{\gamma \in \mathrm{GL}_2(F)} f(x^{-1}\gamma y)$ of a compactly supported function $f$ a locally finite sum. It is used throughout the development of the adelic kernel and its truncations, for instance in the Bruhat-decomposition and transversal-measure computations for that kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_adelicKernelLocalFiniteness.lean

import Definitions.Def_AutomorphicForm_AdelicKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AutomorphicForm.adelicKernelLocalFiniteness (F : Type) [Field F] [NumberField F] :
    AutomorphicForm.AdelicKernelLocalFiniteness F := by sorry
