-- Prove2me | Theorems.Thm_AutomorphicForm_apply_det_heckeGen_pow_inertiaDeg_eq_apply_det_heckeGen_of_comp_idelicNorm_of_unramified
-- name    : AutomorphicForm.apply_det_heckeGen_pow_inertiaDeg_eq_apply_det_heckeGen_of_comp_idelicNorm_of_unramified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/17851c7a-c20d-585f-82a7-dc1435a19b7f
-- title:
--   Base change of idele characters at Hecke generators
-- statement:
--   Let $K$ and $L$ be number fields with a $K$-algebra structure on $L$, and let $\xi_L$, $\xi_K$ be group homomorphisms from the full subgroup $\top$ of the unit groups of the adele rings of $L$ and of $K$ to $\mathbb{C}^\times$ (no continuity or automorphy is assumed). Assume the compatibility: for every idele unit $z$ of $L$, $\xi_K$ evaluated at `idelicNorm` of $z$ for `genuineBaseChange K L` — that is, at the image of $z$ under the units functor applied to the algebra norm of the adele ring of $L$ over that of $K$, taken along the canonical ring morphism — equals $\xi_L(z)$. Let $v$ be a height-one prime of $\mathcal O_K$ and $w$ one of $\mathcal O_L$ with `HeightOneSpectrum.under` of $w$ equal to $v$, and assume $\xi_K$ is unramified at $v$ in the sense that for every unit $t$ of the completion $K_v$ with $\mathrm{v}(t)=1$, the value of $\xi_K$ at the idele which is $t$ at $v$ and $1$ at all other finite places and at the infinite component is $1$. Then, as complex numbers, $\xi_K\bigl(\det \mathrm{heckeGen}(v)\bigr)^{f}=\xi_L\bigl(\det \mathrm{heckeGen}(w)\bigr)$, where $f$ is `Ideal.inertiaDeg'` of $v$ at $w$ and $\mathrm{heckeGen}$ is the diagonal matrix $\mathrm{diag}(\hat\varpi,1)$ built from the chosen uniformiser idele at the place in question. No hypothesis on the ramification of $w$ over $v$ is imposed.
--
--   This is the local compatibility, at an unramified finite place, between an idele character of $K$ and its base change to $L$: the value at the Hecke generator over $K$, raised to the inertia degree, reproduces the value at the Hecke generator over $L$. It is used in the analytic computations with Hecke eigenvalues and Satake parameters that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_det_heckeGen_pow_inertiaDeg_eq_apply_det_heckeGen_of_comp_idelicNorm_of_unramified.lean

import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem AutomorphicForm.apply_det_heckeGen_pow_inertiaDeg_eq_apply_det_heckeGen_of_comp_idelicNorm_of_unramified
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξKN : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξK ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
        ξL ⟨z, Subgroup.mem_top z⟩)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hvw : HeightOneSpectrum.under (𝓞 K) w = v)
    (hur : ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξK ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1) :
    ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^
        v.asIdeal.inertiaDeg' w.asIdeal =
      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by sorry
