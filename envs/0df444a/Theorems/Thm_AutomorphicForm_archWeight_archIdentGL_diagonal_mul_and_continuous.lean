-- Prove2me | Theorems.Thm_AutomorphicForm_archWeight_archIdentGL_diagonal_mul_and_continuous
-- name    : AutomorphicForm.archWeight_archIdentGL_diagonal_mul_and_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/e1cd295b-43fb-5b93-b61c-f8f9b74bc538
-- title:
--   Diagonal invariance and continuity of the archimedean weight
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra. Write $A = L \otimes_K \mathbb{A}_{K,\infty}$ for the tensor product of $L$ with the infinite adele ring of $K$, and let [`AutomorphicForm.archIdentGL`](def/AutomorphicForm_TwistedOrbital.html#L424) $: \mathrm{GL}_2(A) \to \mathrm{GL}_2(\mathbb{A}_{L,\infty})$ be the group homomorphism obtained by applying, entrywise, the ring homomorphism [`AutomorphicForm.archIdent`](def/AutomorphicForm_TwistedOrbital.html#L420), itself the composite of the commutativity isomorphism $L \otimes_K \mathbb{A}_{K,\infty} \cong \mathbb{A}_{K,\infty} \otimes_K L$ with the base-change ring equivalence onto $\mathbb{A}_{L,\infty}$. For $g \in \mathrm{GL}_2(\mathbb{A}_{L,\infty})$ let $H_L(g) =$ [`AutomorphicForm.WindowedSiegel.archHeight L`](def/AutomorphicForm_WindowedSiegelSet.html#L48) $(g) = \prod_{w \mid \infty} \bigl(\lVert \det g_w \rVert / \mathrm{rowNormSq}(g_w)\bigr)^{\mathrm{mult}(w)}$, the product over the infinite places $w$ of $L$ of the local heights of the components $g_w$, and let $W =$ `AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L)` be the image in $\mathrm{GL}_2(\mathbb{A}_{L,\infty})$, under the projection of the adeles of $L$ onto their infinite part, of the adelic point attached to the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix} \in \mathrm{GL}_2(L)$. Put $v(y) = -\log H_L(\iota(y)) - \log H_L(W \cdot \iota(y))$ for $y \in \mathrm{GL}_2(A)$, where $\iota =$ [`AutomorphicForm.archIdentGL`](def/AutomorphicForm_TwistedOrbital.html#L424). The theorem asserts the conjunction of: (i) $v(tx) = v(x)$ for all $t, x \in \mathrm{GL}_2(A)$ such that the $(0,1)$ and $(1,0)$ entries of the matrix underlying $t$ vanish; and (ii) $v$ is continuous on $\mathrm{GL}_2(A)$.
--
--   The function $v$ is the archimedean weight attached to a pair of heights (the identity and the Weyl translate) used in Arthur's weighted orbital integrals, and the two assertions are the invariance under left translation by diagonal elements and the continuity required of such a weight. Both clauses are consumed as hypotheses by the results on twisted weighted orbital integrals and twisted weighted class integrals over the base change $L/K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archWeight_archIdentGL_diagonal_mul_and_continuous.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.archWeight_archIdentGL_diagonal_mul_and_continuous
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    (∀ t x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 0 = 0 →
        (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y))) (t * x) =
        (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y))) x) ∧
    Continuous (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y))) := by sorry
