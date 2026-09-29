-- Prove2me | Theorems.Thm_AutomorphicForm_apply_localUnit_eq_one_of_eq_comp_idelicNorm_of_forall_apply_localUnit_under_eq_one_of_ramificationIdx_eq_one
-- name    : AutomorphicForm.apply_localUnit_eq_one_of_eq_comp_idelicNorm_of_forall_apply_localUnit_under_eq_one_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/5dea44c2-ee3f-58df-b8ad-0d1d92fd2dcf
-- title:
--   Ascent of unramifiedness along the idelic norm
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $\xi_L$ and $\xi_K$ be homomorphisms from the full (top) subgroup of the unit groups of the adele rings $\mathbb{A}_L$ and $\mathbb{A}_K$ to $\mathbb{C}^\times$. Assume compatibility under the norm: for every idele unit $z \in \mathbb{A}_L^\times$, $\xi_K$ evaluated at the idelic norm of $z$ — the image of $z$ under the unit-group map induced by $\mathrm{Algebra.norm}$ for the algebra structure coming from the base-change map `genuineBaseChange` of $\mathbb{A}_K$-algebras $\mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$ — equals $\xi_L(z)$. Let $v$ be a finite place of $K$ and $w$ a finite place of $L$ with $w$ lying over $v$, i.e. $v$ is the prime of $\mathcal{O}_K$ under $w$, and assume the ramification index $e(w \mid v) = 1$. Assume further that $\xi_K$ is trivial on local units at $v$: for every $t \in (K_v)^\times$ with $|t|_v = 1$, the value of $\xi_K$ at the idele which is $t$ at $v$ and $1$ at all other finite places and at the infinite component is $1$. Then the same holds for $\xi_L$ at $w$: for every $s \in (L_w)^\times$ with $|s|_w = 1$, $\xi_L$ of the idele which is $s$ at $w$ and $1$ elsewhere equals $1$.
--
--   This is the ascent half of the comparison of conductors under base change: an idele class character of $K$ unramified at $v$ pulls back, along the idelic norm, to a character of $L$ unramified at any $w \mid v$ with $e(w\mid v) = 1$. It feeds the analysis of local behaviour of automorphic forms used downstream in [`AutomorphicForm.exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine`](thm.html#AutomorphicForm.exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_localUnit_eq_one_of_eq_comp_idelicNorm_of_forall_apply_localUnit_under_eq_one_of_ramificationIdx_eq_one.lean

import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem AutomorphicForm.apply_localUnit_eq_one_of_eq_comp_idelicNorm_of_forall_apply_localUnit_under_eq_one_of_ramificationIdx_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξKN : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξK ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
        ξL ⟨z, Subgroup.mem_top z⟩)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hvw : HeightOneSpectrum.under (𝓞 K) w = v)
    (he : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hur : ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξK ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)
    (s : (w.adicCompletion L)ˣ) (hs : Valued.v (s : w.adicCompletion L) = 1) :
    ξL ⟨Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L w s), Subgroup.mem_top _⟩ = 1 := by sorry
