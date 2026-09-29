-- Prove2me | Theorems.Thm_AutomorphicForm_apply_localUnit_eq_one_of_comp_idelicNorm_of_forall_apply_localUnit_eq_one_of_ramificationIdx_eq_one
-- name    : AutomorphicForm.apply_localUnit_eq_one_of_comp_idelicNorm_of_forall_apply_localUnit_eq_one_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/291dcd8e-8b8a-51d9-9d13-2953a8d922db
-- title:
--   Unramified descent of an idele class character along the norm
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$, and let $\xi_L$ and $\xi_K$ be multiplicative characters with values in $\mathbb{C}^\times$ defined on the full subgroups $\top$ of $(\mathbf{A}_L)^\times$ and $(\mathbf{A}_K)^\times$ respectively, the adele rings being those attached to $\mathcal{O}_L \subset L$ and $\mathcal{O}_K \subset K$. Assume the compatibility $\xi_K(N(z)) = \xi_L(z)$ for every unit $z$ of the adele ring of $L$, where $N$ is the idelic norm of the base change `genuineBaseChange`, i.e. the map induced on unit groups by the algebra norm of $\mathbf{A}_L$ over $\mathbf{A}_K$ for the algebra structure coming from the ring homomorphism $\mathbf{A}_K \to \mathbf{A}_L$ of that base-change datum. Let $v$ be a nonzero prime of $\mathcal{O}_K$ and $w$ one of $\mathcal{O}_L$ with $w$ lying over $v$ (the prime of $\mathcal{O}_K$ under $w$ being $v$), and assume the ramification index $e(w \mid v) = 1$. Assume further that for every unit $s$ of the completion $L_w$ with $\mathrm{v}(s) = 1$, the value of $\xi_L$ at the idele which is $s$ in the component at $w$, $1$ at all other finite components and $1$ at the infinite component, equals $1$. Then for every unit $t$ of $K_v$ with $\mathrm{v}(t) = 1$, the value of $\xi_K$ at the idele which is $t$ at $v$ and $1$ elsewhere equals $1$.
--
--   This is the descent, along the norm map of an unramified extension of local fields, of the statement that an idele class character is unramified at a finite place: triviality on the local units at $w$ forces triviality on the local units at $v$ when $e(w \mid v) = 1$. It serves as the interface between the unramifiedness criterion for characters of the idele group and the packaging of idele class characters used in the hyperbolic-term computations that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_localUnit_eq_one_of_comp_idelicNorm_of_forall_apply_localUnit_eq_one_of_ramificationIdx_eq_one.lean

import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem AutomorphicForm.apply_localUnit_eq_one_of_comp_idelicNorm_of_forall_apply_localUnit_eq_one_of_ramificationIdx_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξKN : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξK ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
        ξL ⟨z, Subgroup.mem_top z⟩)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hvw : HeightOneSpectrum.under (𝓞 K) w = v)
    (he : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hurL : ∀ s : (w.adicCompletion L)ˣ, Valued.v (s : w.adicCompletion L) = 1 →
      ξL ⟨Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L w s), Subgroup.mem_top _⟩ = 1)
    (t : (v.adicCompletion K)ˣ) (ht : Valued.v (t : v.adicCompletion K) = 1) :
    ξK ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1 := by sorry
