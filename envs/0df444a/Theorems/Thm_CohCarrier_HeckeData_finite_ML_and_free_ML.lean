-- Prove2me | Theorems.Thm_CohCarrier_HeckeData_finite_ML_and_free_ML
-- name    : CohCarrier.HeckeData.finite_ML_and_free_ML
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/ed26877e-87a2-5b06-aef7-bbf23675680b
-- title:
--   Finiteness and freeness of the localised Hecke module
-- statement:
--   Let $\mathcal O$ be a commutative local Noetherian ring which is complete (in the adic sense) for its maximal ideal, let $V$ be an $\mathcal O$-module that is finite over $\mathcal O$, and let $k$ be a field equipped with an $\mathcal O$-algebra structure whose structure map $\mathcal O \to k$ is surjective (so that $k$ is the residue field of $\mathcal O$). Let $D$ be a [`CohCarrier.HeckeData`](def/CohCarrier_HeckeData.html#L14) for these data, that is: an index type $D.\mathrm{Gen}$, a family $D.\mathrm{op}$ of $\mathcal O$-linear endomorphisms of $V$ indexed by it, a proof that any two of these endomorphisms commute in $\operatorname{End}_{\mathcal O}(V)$, and a function $D.\overline\theta$ from the index type to $k$. Write `D.FreeAlg` for the free commutative $\mathcal O$-algebra on $D.\mathrm{Gen}$, `D.opAlgHom` for the $\mathcal O$-algebra map to $\operatorname{End}_{\mathcal O}(V)$ determined by $D.\mathrm{op}$, `D.thetaTilde` for the $\mathcal O$-algebra map to $k$ determined by $D.\overline\theta$, and `D.mTheta` for its kernel; the module `D.ML` is the localisation of $V$, viewed over `D.FreeAlg` through `D.opAlgHom`, at the complement of the prime `D.mTheta`. The conclusion is the conjunction: `D.ML` is a finite $\mathcal O$-module, and, if $V$ is free over $\mathcal O$, then `D.ML` is free over $\mathcal O$ (freeness of $V$ being a hypothesis only of the second clause).
--
--   This is the basic finiteness statement for the localisation of a cohomology carrier at the residual eigensystem $\overline\theta$ of a commuting family of Hecke operators, giving that the localised module is again finite over the complete local coefficient ring, and free when the carrier is. It underlies the later comparisons of localised Hecke modules, for instance [`CohCarrier.HeckeData.exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem`](thm.html#CohCarrier.HeckeData.exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem), [`CohCarrier.HeckeData.exists_linearEquiv_ML_prod_of_companion`](thm.html#CohCarrier.HeckeData.exists_linearEquiv_ML_prod_of_companion) and [`CuspForm.AuxLevel.exists_linearEquiv_baseML_prod_ML`](thm.html#CuspForm.AuxLevel.exists_linearEquiv_baseML_prod_ML).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_HeckeData_finite_ML_and_free_ML.lean

import Definitions.Def_CohCarrier_HeckeData
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.HeckeData.finite_ML_and_free_ML {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    [IsNoetherianRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (D : CohCarrier.HeckeData 𝒪 V k) :
    Module.Finite 𝒪 D.ML ∧ (Module.Free 𝒪 V → Module.Free 𝒪 D.ML) := by sorry
