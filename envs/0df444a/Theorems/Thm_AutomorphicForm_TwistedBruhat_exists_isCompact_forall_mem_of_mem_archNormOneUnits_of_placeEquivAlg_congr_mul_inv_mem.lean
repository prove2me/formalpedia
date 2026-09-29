-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_mem_of_mem_archNormOneUnits_of_placeEquivAlg_congr_mul_inv_mem
-- name    : AutomorphicForm.TwistedBruhat.exists_isCompact_forall_mem_of_mem_archNormOneUnits_of_placeEquivAlg_congr_mul_inv_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/97a2cf49-507d-56f9-814d-13b88f331548
-- title:
--   Compactness of archimedean norm-one units with bounded σ-ratio
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ Galois, let $\sigma$ be a $K$-automorphism of $L$ such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$ (so the Galois group is cyclic with generator $\sigma$), and let $v$ be an infinite place of $K$. Write $v.\mathrm{Extension}\,L$ for the set of infinite places $w$ of $L$ with $w \circ \mathrm{algebraMap}\,K\,L = v$, and consider the unit group of the semilocal ring $\prod_{w \mid v} L_w$ of completions. Let $C$ be a compact set of such units. The assertion is the existence of a compact set $B$ of units of $\prod_{w \mid v} L_w$ with the following property: for every unit $x$ which lies in `archNormOneUnits K L v`, that is, in the kernel of the monoid homomorphism sending $x$ to $\mathrm{normHom}_v\bigl(N_{\prod_w L_w / K_v}(x)\bigr)$ (the $v$-absolute value of the $K_v$-algebra norm of $x$ equals $1$), and such that the product of $\sigma_v(x)$ with the value of $x^{-1}$ equals the value of some element of $C$, one has $x \in B$. Here $\sigma_v$ denotes the automorphism of $\prod_{w\mid v} L_w$ obtained by transporting $\mathrm{id}_{K_v} \otimes \sigma$ along the $K_v$-algebra isomorphism `placeEquivAlg` $: K_v \otimes_K L \cong \prod_{w \mid v} L_w$.
--
--   This is the archimedean counterpart of the cyclic-ratio compactness lemma: a compact bound on the ratio $\sigma_v(x)x^{-1}$, together with the norm-one condition, confines $x$ itself to a compact set of semilocal units. It is used in the twisted Bruhat and transversal-measure estimates for the cyclic base-change trace pushforward, being cited by [`AutomorphicForm.TwistedBruhat.exists_isCompact_forall_ae_mem_of_unitsAct_mul_inv_mem_of_transversal_unram`](thm.html#AutomorphicForm.TwistedBruhat.exists_isCompact_forall_ae_mem_of_unitsAct_mul_inv_mem_of_transversal_unram) and by [`AutomorphicForm.TwistedBruhat.exists_isCompact_forall_mem_of_forall_archFibre_mem_archNormOneUnits_of_map_mul_inv_mem`](thm.html#AutomorphicForm.TwistedBruhat.exists_isCompact_forall_mem_of_forall_archFibre_mem_archNormOneUnits_of_map_mul_inv_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_mem_of_mem_archNormOneUnits_of_placeEquivAlg_congr_mul_inv_mem.lean

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
import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_M4aHerbrand_ArchSemilocal
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal
open scoped TensorProduct.RightActions in
attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel
  AutomorphicForm.TransversalMeasure.archUnitsBorel in

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

theorem AutomorphicForm.TwistedBruhat.exists_isCompact_forall_mem_of_mem_archNormOneUnits_of_placeEquivAlg_congr_mul_inv_mem
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : InfinitePlace K)
    (C : Set ((w : v.Extension L) → w.1.Completion)ˣ) (hC : IsCompact C) :
    ∃ B : Set ((w : v.Extension L) → w.1.Completion)ˣ, IsCompact B ∧
      ∀ x : ((w : v.Extension L) → w.1.Completion)ˣ,
        x ∈ AutomorphicForm.TransversalMeasure.archNormOneUnits K L v →
        M4aHerbrand.ArchSemilocal.placeEquivAlg (K := K) (L := L) v
            ((Algebra.TensorProduct.congr (AlgEquiv.refl : v.Completion ≃ₐ[v.Completion] v.Completion) σ)
              ((M4aHerbrand.ArchSemilocal.placeEquivAlg (K := K) (L := L) v).symm
                ((x : ((w : v.Extension L) → w.1.Completion)ˣ) : (w : v.Extension L) → w.1.Completion))) *
          (((x⁻¹ : ((w : v.Extension L) → w.1.Completion)ˣ)) : (w : v.Extension L) → w.1.Completion) ∈
          (Units.val : ((w : v.Extension L) → w.1.Completion)ˣ → ((w : v.Extension L) → w.1.Completion)) '' C →
        x ∈ B := by sorry
