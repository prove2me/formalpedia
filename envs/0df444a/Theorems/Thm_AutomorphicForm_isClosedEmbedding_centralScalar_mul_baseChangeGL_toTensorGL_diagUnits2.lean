-- Prove2me | Theorems.Thm_AutomorphicForm_isClosedEmbedding_centralScalar_mul_baseChangeGL_toTensorGL_diagUnits2
-- name    : AutomorphicForm.isClosedEmbedding_centralScalar_mul_baseChangeGL_toTensorGL_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/3d127050-74c3-5415-82dd-063ec5d818b0
-- title:
--   The torus chart (z,a)↦ zcdotbc(diag(a,1)) is a closed embedding
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$. Consider the map
--   $$\theta:(\mathbb{A}_L)^\times\times(\mathbb{A}_K)^\times\longrightarrow \mathrm{GL}_2(\mathbb{A}_L),\qquad \theta(z,a)=\mathrm{centralScalar}(z)\cdot \mathrm{baseChangeGL}\bigl(\mathrm{toTensorGL}(\mathrm{diag}(a,1))\bigr),$$ where $\mathbb{A}_K=\mathrm{AdeleRing}(\mathcal{O}_K,K)$ and $\mathbb{A}_L=\mathrm{AdeleRing}(\mathcal{O}_L,L)$. Here [`AutomorphicForm.centralScalar`](def/AutomorphicForm_AdelicLsXi.html#L18) is $z\mapsto z\cdot 1_2$, the scalar embedding of $(\mathbb{A}_L)^\times$ into $\mathrm{GL}_2(\mathbb{A}_L)$; `diagUnits2 p.2 1` is the invertible $2\times 2$ matrix $\mathrm{diag}(a,1)$ over $\mathbb{A}_K$ with its explicit inverse $\mathrm{diag}(a^{-1},1)$; [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) applies the $K$-algebra map $x\mapsto 1\otimes x$ entrywise, landing in $\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$; and [`AutomorphicForm.baseChangeGL`](def/AutomorphicForm_BaseChangePlaces.html#L69) applies entrywise the ring isomorphism $L\otimes_K\mathbb{A}_K\cong\mathbb{A}_L$ given by commuting the tensor factors followed by [`M4aHerbrand.Bridge.genuineRingEquiv`](def/M4aHerbrand_GenuineTensorEquiv.html#L57). The assertion is that $\theta$, with the product topology on the source and the topology of $\mathrm{GL}_2(\mathbb{A}_L)$ on the target, is a closed embedding, i.e. a topological embedding with closed range.
--
--   This is the chart parametrising the subgroup $Z(\mathbb{A}_L)\,A(\mathbb{A}_K)$ of $\mathrm{GL}_2(\mathbb{A}_L)$ arising in the base-change (twisted-orbital) unfolding; closedness of the embedding is what transports compact support along the chart. It is cited in the proof of [`AutomorphicForm.integral_subgroup_centralScalar_twistedOrbital_mul_section_eq_const_mul_integral_ker_idelicNorm`](thm.html#AutomorphicForm.integral_subgroup_centralScalar_twistedOrbital_mul_section_eq_const_mul_integral_ker_idelicNorm), and it rests on the closed embedding property of the induced map $(\mathbb{A}_K)^\times\to(\mathbb{A}_L)^\times$ recorded in [`M4aHerbrand.GenuineDescent.isClosedEmbedding_unitsMap_genuineBaseChange`](thm.html#M4aHerbrand.GenuineDescent.isClosedEmbedding_unitsMap_genuineBaseChange).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isClosedEmbedding_centralScalar_mul_baseChangeGL_toTensorGL_diagUnits2.lean

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

theorem AutomorphicForm.isClosedEmbedding_centralScalar_mul_baseChangeGL_toTensorGL_diagUnits2
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Topology.IsClosedEmbedding (fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ =>
      AutomorphicForm.centralScalar (𝓞 L) L p.1 *
        AutomorphicForm.baseChangeGL K L
          (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.2 1))) := by sorry
