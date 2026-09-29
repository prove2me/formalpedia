-- Prove2me | Theorems.Thm_AutomorphicForm_archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2
-- name    : AutomorphicForm.archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/78f5d617-ba03-589e-9c23-8cdd1d65202f
-- title:
--   Galois action preserves archimedean height and finite integrality
-- statement:
--   Let $K$ and $L$ be fields with $L$ a number field and an algebra over $K$, and let $D$ be an idèle Galois descent datum for $\mathcal O_L \subset L$ over $K$, that is, a monoid homomorphism $D.\mathrm{act}$ from the group $L \simeq_{\mathrm{alg}[K]} L$ of $K$-algebra automorphisms of $L$ to the ring automorphisms of the adele ring $\mathbb A_L =$ `AdeleRing (𝓞 L) L`, satisfying $D.\mathrm{act}\,g\,(x) = (g\,x)$ on principal adeles and continuity of each $D.\mathrm{act}\,g$. Fix such an automorphism $\sigma$ and an element $g$ of $\mathrm{GL}_2(\mathbb A_L)$, and let $\sigma \cdot g$ denote `sigmaAdelicAct K L D σ g`, the image of $g$ under the entrywise application of the ring automorphism $D.\mathrm{act}\,\sigma$. Two assertions are made. First, the archimedean heights of $g$ and $\sigma\cdot g$ agree: writing $\mathrm{glArch}$ for the entrywise projection of $\mathrm{GL}_2(\mathbb A_L)$ to $\mathrm{GL}_2$ of the infinite adeles, and $\mathrm{archHeight}(h) = \prod_{v} \bigl(\|\det h_v\|/\mathrm{rowNormSq}(h_v)\bigr)^{v.\mathrm{mult}}$, the product over the infinite places $v$ of $L$ of the local heights of the components $h_v$ raised to the local degrees, one has $\mathrm{archHeight}(\mathrm{glArch}(\sigma\cdot g)) = \mathrm{archHeight}(\mathrm{glArch}(g))$. Second, if the finite-adelic part $\mathrm{glFin}(g)$ lies in `finiteIntegralGL2`, the subgroup of $\mathrm{GL}_2$ of the finite adeles consisting of those $h$ for which both $h$ and $h^{-1}$ satisfy the predicate `IsLevelZeroMatrix` at the unit ideal $\top$, then so does $\mathrm{glFin}(\sigma\cdot g)$.
--
--   This records the invariance of the two defining constraints of a windowed Siegel set — the archimedean height and integrality of the finite part — under the Galois action on $\mathrm{GL}_2$ of the adeles, so that the Galois twist of an automorphic form may be estimated on the same sets as the form itself. It is used in the estimates for twisted adelic kernels and their constant terms on centre-cut Siegel sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_WindowedSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.WindowedSiegel.archHeight L
        (NumberField.AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g)) =
      AutomorphicForm.WindowedSiegel.archHeight L (NumberField.AdelicLevel.glArch (𝓞 L) L g) ∧
    (NumberField.AdelicLevel.glFin (𝓞 L) L g ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 L) L →
      NumberField.AdelicLevel.glFin (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g) ∈
        NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 L) L) := by sorry
