-- Prove2me | Theorems.Thm_AutomorphicForm_measure_setOf_algebraNorm_det_sum_map_tmul_eq_zero_eq_zero_of_isUnit
-- name    : AutomorphicForm.measure_setOf_algebraNorm_det_sum_map_tmul_eq_zero_eq_zero_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/88dda91c-a752-5f15-b930-b56dcb6a146c
-- title:
--   Haar-nullity of the norm-zero locus in M₂(L⊗_K Kᵥ)
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a nonzero prime of the ring of integers $\mathcal{O}_K$ (an element of the height-one spectrum), and let $K_v$ denote the $v$-adic completion of $K$, carrying the Borel $\sigma$-algebra of its topology. Let $\iota$ be a finite index type, let $b : \iota \to M_2(L)$ be a family of $2\times 2$ matrices over $L$, and for $a \in K_v^{\iota}$ write $A(a) = \sum_{i} (b_i \otimes a_i) \in M_2(L\otimes_K K_v)$, meaning the sum over $i$ of the matrix obtained from $b_i$ by applying $l \mapsto l \otimes_K a_i$ entrywise. Assume there is some $a_0 \in K_v^{\iota}$ for which $\det A(a_0)$ is a unit of the ring $L \otimes_K K_v$. Then for every additive Haar measure $\mu$ on $K_v^{\iota}$, the set of $a \in K_v^{\iota}$ with $\mathrm{N}_{(L\otimes_K K_v)/K_v}(\det A(a)) = 0$, the algebra norm over $K_v$ of $\det A(a)$, has $\mu$-measure zero.
--
--   This is the measure-theoretic input saying that in the linear coordinates $a \mapsto \sum_i b_i \otimes a_i$ on a finite $K_v$-algebra of $2\times 2$ matrices, the locus of non-units is Haar-null as soon as one point of the chart is a unit. It is used in the local additive-to-multiplicative comparisons of orbital integrals over twisted centralisers, where $b$ runs through a $K$-basis of a twisted commutant and $a_0$ gives the coordinates of the identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_measure_setOf_algebraNorm_det_sum_map_tmul_eq_zero_eq_zero_of_isUnit.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_TwistedCommutant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox
  NumberField.TateGlobal IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem AutomorphicForm.measure_setOf_algebraNorm_det_sum_map_tmul_eq_zero_eq_zero_of_isUnit
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (b : ι → Matrix (Fin 2) (Fin 2) L)
    (a₀ : ι → v.adicCompletion K)
    (h1 : IsUnit (Matrix.det (∑ i : ι, (b i).map fun l : L => l ⊗ₜ[K] a₀ i :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (ι → v.adicCompletion K)) [μ.IsAddHaarMeasure] :
    μ {a : ι → v.adicCompletion K |
        Algebra.norm (v.adicCompletion K) (Matrix.det (∑ i : ι, (b i).map fun l : L => l ⊗ₜ[K] a i :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) = 0} = 0 := by sorry
