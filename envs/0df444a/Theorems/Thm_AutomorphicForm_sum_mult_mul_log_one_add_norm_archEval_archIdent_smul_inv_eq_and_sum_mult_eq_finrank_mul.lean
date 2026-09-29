-- Prove2me | Theorems.Thm_AutomorphicForm_sum_mult_mul_log_one_add_norm_archEval_archIdent_smul_inv_eq_and_sum_mult_eq_finrank_mul
-- name    : AutomorphicForm.sum_mult_mul_log_one_add_norm_archEval_archIdent_smul_inv_eq_and_sum_mult_eq_finrank_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/7735ac0e-8b40-5082-b18d-dd4840d3d4d5
-- title:
--   Local log splitting above an archimedean place of K
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ a finite Galois extension, let $w$ be an infinite place of $K$, let $c$ be a unit of the infinite adele ring $K_\infty$ of $K$, and let $x \in L \otimes_K K_\infty$. Write $\iota =$ [`AutomorphicForm.archIdent K L`](def/AutomorphicForm_TwistedOrbital.html#L420) for the ring homomorphism $L \otimes_K K_\infty \to L_\infty$ obtained by composing the commutativity isomorphism $L \otimes_K K_\infty \simeq K_\infty \otimes_K L$ with the base-change ring isomorphism $K_\infty \otimes_K L \simeq L_\infty$ attached to `genuineInfinitePlaceData`, and write $y \mapsto y_{w'}$ for evaluation `archEval` of an infinite adele at a place, landing in the completion at that place. Three assertions are made. First, for every infinite place $w'$ of $L$ whose restriction along $K \to L$ is $w$, one has $\|\iota(c^{-1} \cdot x)_{w'}\| = \|\iota(x)_{w'}\| / \|c_w\|$, the scalar action being that of $K_\infty$ on $L \otimes_K K_\infty$. Secondly, summing over the places $w'$ of $L$ restricting to $w$, with $m_{w'}$ the multiplicity $1$ or $2$ of $w'$, $$\sum_{w' \mid w} m_{w'} \log\bigl(1 + \|\iota(c^{-1}\cdot x)_{w'}\|^2\bigr) = \sum_{w' \mid w} m_{w'}\Bigl(\log\bigl(\|c_w\|^2 + \|\iota(x)_{w'}\|^2\bigr) - 2\log\|c_w\|\Bigr).$$ Thirdly, $\sum_{w' \mid w} m_{w'} = [L:K]\, m_w$, an identity of natural numbers.
--
--   The first clause records the compatibility of the archimedean absolute values of $L$ above $w$ with that of $K$ at $w$ through the identification of $L \otimes_K K_\infty$ with $L_\infty$, and the third is the archimedean local degree formula for a place of $K$ in a finite extension. Together they split the logarithmic weight layer occurring in the twisted orbital computations into a main term $-2[L:K]m_w\log\|c_w\|$ and logarithmic potentials; the result is used in the analysis of norms of resolvents at archimedean places and in the evaluation of twisted integrals against the logarithmic weight.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sum_mult_mul_log_one_add_norm_archEval_archIdent_smul_inv_eq_and_sum_mult_eq_finrank_mul.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped ENNReal Classical

theorem AutomorphicForm.sum_mult_mul_log_one_add_norm_archEval_archIdent_smul_inv_eq_and_sum_mult_eq_finrank_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (w : NumberField.InfinitePlace K) (c : (InfiniteAdeleRing K)ˣ) (x : L ⊗[K] InfiniteAdeleRing K) :
    (∀ w' : NumberField.InfinitePlace L, w'.comap (algebraMap K L) = w →
      ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L
          (((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • x))‖ =
        ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L x)‖ /
          ‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖) ∧
    (∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
        (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L
          (((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • x))‖ ^ 2) =
      ∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
        (w'.mult : ℝ) * (Real.log (‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖ ^ 2 +
            ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L x)‖ ^ 2) -
          2 * Real.log ‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖)) ∧
    (∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w), w'.mult =
      Module.finrank K L * w.mult) := by sorry
