-- Prove2me | Theorems.Thm_AutomorphicForm_norm_tensorPlace_apply_eq_algebraMap_norm_of_baseChangeGL_eq_globalPoints
-- name    : AutomorphicForm.norm_tensorPlace_apply_eq_algebraMap_norm_of_baseChangeGL_eq_globalPoints
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/c1d44dc4-1a97-5cba-ab34-c34eb459a350
-- title:
--   Entrywise norms of a base-change lift are global norms
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $t \in \mathrm{GL}_2(L)$ and let $\delta \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, where $\mathbb{A}_K$ is the adele ring of $K$. Assume that the image of $\delta$ under the map of general linear groups induced by the ring isomorphism $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_L$ (the commutativity isomorphism of the tensor product followed by [`M4aHerbrand.Bridge.genuineRingEquiv`](def/M4aHerbrand_GenuineTensorEquiv.html#L57)) coincides with the image of $t$ under the map of general linear groups induced by the structure map $L \to \mathbb{A}_L$. Fix indices $i, j \in \{0,1\}$. Then two assertions hold. First, for every height-one prime $v$ of $\mathcal{O}_K$, the algebra norm over $K_v$ of the $(i,j)$ entry of the matrix of [`AutomorphicForm.tensorPlace K L v δ`](def/AutomorphicForm_BaseChangePlaces.html#L49) — the image of $\delta$ under $\mathrm{id}_L \otimes (\mathbb{A}_K \to K_v)$ — equals the image under $K \to K_v$ of $N_{L/K}(t_{ij})$. Second, the algebra norm over the infinite adele ring $\mathbb{A}_{K,\infty}$ of the $(i,j)$ entry of the matrix of [`AutomorphicForm.tensorArch K L δ`](def/AutomorphicForm_BaseChangePlaces.html#L46) — the image of $\delta$ under $\mathrm{id}_L \otimes (\mathbb{A}_K \to \mathbb{A}_{K,\infty})$ — equals the image under $K \to \mathbb{A}_{K,\infty}$ of $N_{L/K}(t_{ij})$.
--
--   This is the compatibility of the algebra norm with base change, applied entrywise to a matrix in $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ which comes from a global matrix over $L$. It lets local and archimedean weights formed from the norms of the entries of such a $\delta$ be recognised as the absolute values, at the corresponding places, of one element of $K^\times$, and is used in this form in the bounds for twisted orbital integrals over double cosets and in the archimedean estimate for `isTwistedOrbitalIntegralOn`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_norm_tensorPlace_apply_eq_algebraMap_norm_of_baseChangeGL_eq_globalPoints.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.norm_tensorPlace_apply_eq_algebraMap_norm_of_baseChangeGL_eq_globalPoints
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (t : GL (Fin 2) L) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t) (i j : Fin 2) :
    (∀ v : HeightOneSpectrum (𝓞 K),
      Algebra.norm (v.adicCompletion K)
          ((AutomorphicForm.tensorPlace K L v δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j) =
        algebraMap K (v.adicCompletion K) (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) i j))) ∧
    Algebra.norm (InfiniteAdeleRing K)
        ((AutomorphicForm.tensorArch K L δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) i j) =
      algebraMap K (InfiniteAdeleRing K) (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) i j)) := by sorry
