-- Prove2me | solution 1 for isNormableSpace_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:02:10.49732+00:00
-- url     : https://prove2.me/submissions/3ced1099-d13c-4dcd-a03c-513fb9b8aaa2

import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_ImportCompatibility_Normability
import Theorems.Thm_Topology_IsInducing_isNormableSpace
import Theorems.Thm_ContinuousLinearEquiv_isNormableSpace
section
open Topology
section NormabilityBackport
variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
end NormabilityBackport
section NormabilityBackport
variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [t : TopologicalSpace E] [hn : IsNormableSpace 𝕜 E]
variable (𝕜 E)
end NormabilityBackport
section Transport
variable {𝕜 E F : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
end Transport
section FiniteDimensionalBackport
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]
variable (E) in
private lemma isNormableSpace_of_t2Space_finiteDimensional
    [T2Space E] [FiniteDimensional 𝕜 E] : IsNormableSpace 𝕜 E := by
  have e : E ≃L[𝕜] (Module.Basis.ofVectorSpaceIndex 𝕜 E) → 𝕜 :=
    (Module.Basis.ofVectorSpace 𝕜 E).equivFun.toContinuousLinearEquiv
  exact e.isNormableSpace
end FiniteDimensionalBackport
end

set_option autoImplicit true
open Topology
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]
theorem _root_.solution [FiniteDimensional 𝕜 E] : IsNormableSpace 𝕜 E := by
  let F := SeparationQuotient E
  have : IsNormableSpace 𝕜 F := isNormableSpace_of_t2Space_finiteDimensional _
  let f : E →ₗ[𝕜] F := SeparationQuotient.mkCLM 𝕜 E
  have : IsInducing f := SeparationQuotient.isInducing_mk
  exact this.isNormableSpace
