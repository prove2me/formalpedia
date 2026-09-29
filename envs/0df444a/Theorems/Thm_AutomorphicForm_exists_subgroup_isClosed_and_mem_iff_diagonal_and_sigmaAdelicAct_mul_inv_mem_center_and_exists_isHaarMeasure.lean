-- Prove2me | Theorems.Thm_AutomorphicForm_exists_subgroup_isClosed_and_mem_iff_diagonal_and_sigmaAdelicAct_mul_inv_mem_center_and_exists_isHaarMeasure
-- name    : AutomorphicForm.exists_subgroup_isClosed_and_mem_iff_diagonal_and_sigmaAdelicAct_mul_inv_mem_center_and_exists_isHaarMeasure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/6b948c8d-e662-5a04-bcab-0dba0080905c
-- title:
--   A closed twisted diagonal subgroup of GL₂(A_L) carrying Haar measure
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$, let $D$ be an idele Galois descent datum for $\mathcal{O}_L$, $K$, $L$ — that is, a monoid homomorphism `D.act` from the group $L \simeq_{\mathrm{alg}[K]} L$ of $K$-algebra automorphisms of $L$ to the ring automorphisms of the adele ring $\mathbb{A}_L$ of $L$, compatible with the structure map $L \to \mathbb{A}_L$ in the sense that `D.act g` carries the image of $x \in L$ to the image of $g(x)$, and with each `D.act g` continuous — and let $\sigma$ be a $K$-algebra automorphism of $L$. The adelic group in play is $G = \mathrm{GL}_2(\mathbb{A}_L)$, equipped with the Borel $\sigma$-algebra of its topology. The assertion is that there exists a subgroup $H \le G$ such that: the underlying set of $H$ is closed in $G$; an element $h \in G$ lies in $H$ precisely when the matrix entries $h_{1,0}$ and $h_{0,1}$ both vanish and $\sigma_D(h)\,h^{-1}$ lies in the centre of $G$, where $\sigma_D$ denotes the endomorphism [`AutomorphicForm.sigmaAdelicAct K L D σ`](def/AutomorphicForm_SigmaAdelicAction.html#L14) of $G$ obtained by applying the ring automorphism `D.act σ` of $\mathbb{A}_L$ entrywise; and there exists a measure $\mu_H$ on $H$ which is a Haar measure (in particular left-invariant) and is also right-invariant.
--
--   The subgroup described is the twisted diagonal torus, or twisted centraliser, attached to $\sigma$ in the twisted trace formula for base change on $\mathrm{GL}(2)$; the statement packages it together with a bi-invariant Haar measure. It is used by the rows treating the hyperbolic terms and the associated twisted orbital integrals, which take such a quadruple (subgroup, closedness, membership characterisation, measure) as input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_subgroup_isClosed_and_mem_iff_diagonal_and_sigmaAdelicAct_mul_inv_mem_center_and_exists_isHaarMeasure.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_subgroup_isClosed_and_mem_iff_diagonal_and_sigmaAdelicAct_mul_inv_mem_center_and_exists_isHaarMeasure
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    ∃ H : Subgroup (AdelicGL2 (𝓞 L) L), IsClosed (H : Set (AdelicGL2 (𝓞 L) L)) ∧
      (∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
        ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
         (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
         AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L))) ∧
      ∃ μH : Measure H, μH.IsHaarMeasure ∧ μH.IsMulRightInvariant := by sorry
