-- Prove2me | Theorems.Thm_AutomorphicForm_isOpen_and_isCompact_and_nonempty_and_exists_box_subset_of_forall_semiLocalEval_mem
-- name    : AutomorphicForm.isOpen_and_isCompact_and_nonempty_and_exists_box_subset_of_forall_semiLocalEval_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/8e8da03a-e38e-5830-95d9-daf846be0e1c
-- title:
--   Compact open adelic level set from prescribed semi-local data
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $S_1$ be a finite set of height-one primes of $\mathcal{O}_K$, and for each height-one prime $v$ of $\mathcal{O}_K$ let $U_v \subseteq (L \otimes_K K_v)^2$ be a set of pairs, written as functions $\mathrm{Fin}\,2 \to L \otimes_K K_v$. Assume that for $v \in S_1$ the set $U_v$ is open, compact and contains $0$, and that for $v \notin S_1$ it is exactly the set of pairs both of whose coordinates lie in the image of $\mathcal{O}_L \otimes_{\mathcal{O}_K} \mathcal{O}_{K_v} \to L \otimes_K K_v$ (the semi-local integers). Let $U$ be the set of pairs $a$ of finite adeles of $L$ such that for every $v$ the pair of semi-local evaluations $i \mapsto \mathrm{semiLocalEval}_v(a_i)$ lies in $U_v$, where the semi-local evaluation at $v$ sends a finite adele of $L$ to its tuple of components at the places $w$ of $L$ above $v$, transported back along the inverse of the isomorphism $L \otimes_K K_v \cong \prod_{w \mid v} L_w$. Then $U$ is open, compact and non-empty, and there is an integer $n > 0$ such that for every pair $x$ of finite adeles of $L$ with all components integral at every place, the pair $(n x_i)_i$ lies in $U$.
--
--   This is the adelic-topology half of the choice of level for a standard test function: the local data $U_v$ are the prescribed column sets at the finitely many exceptional places, and the conclusion supplies openness, compactness, non-emptiness and the containment $n\widehat{\mathcal{O}}_L^{\,2} \subseteq U$ of a scaled integral box. It feeds the level-choice statement comparing an indicator of a matrix-vector condition with a product of local indicators, and it uses the local constancy and compact support of indicators built from semi-local evaluations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isOpen_and_isCompact_and_nonempty_and_exists_box_subset_of_forall_semiLocalEval_mem.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Topology

open scoped Classical

theorem AutomorphicForm.isOpen_and_isCompact_and_nonempty_and_exists_box_subset_of_forall_semiLocalEval_mem
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (S₁ : Finset (HeightOneSpectrum (𝓞 K)))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 K), Set (Fin 2 → L ⊗[K] v.adicCompletion K))
    (hUo : ∀ v ∈ S₁, IsOpen (Uloc v)) (hUc : ∀ v ∈ S₁, IsCompact (Uloc v))
    (hU0 : ∀ v ∈ S₁, (0 : Fin 2 → L ⊗[K] v.adicCompletion K) ∈ Uloc v)
    (hUstd : ∀ v ∉ S₁, Uloc v = {x | ∀ i, x i ∈ AutomorphicForm.semiLocalIntegers K L v})
    (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L))
    (hU : U = {a | ∀ v : HeightOneSpectrum (𝓞 K), (fun i => AutomorphicForm.semiLocalEval K L v (a i)) ∈ Uloc v}) :
    IsOpen U ∧ IsCompact U ∧ U.Nonempty ∧
      ∃ n : ℕ, 0 < n ∧ ∀ x : Fin 2 → FiniteAdeleRing (𝓞 L) L,
        (∀ i, x i ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L) →
          (fun i => ((n : ℕ) : FiniteAdeleRing (𝓞 L) L) * x i) ∈ U := by sorry
