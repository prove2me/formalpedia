-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isArchKFinite_equivariant_integral_maximalCompactAtHaar_mul_ne_zero
-- name    : AutomorphicForm.exists_isArchKFinite_equivariant_integral_maximalCompactAtHaar_mul_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/eda08b89-28ae-5487-8a01-ab4f3bc884a3
-- title:
--   Non-vanishing pairing of a ν-covariant kernel with an arch-finite function
-- statement:
--   Let $K$ be a number field, write $\mathbb{A}_K$ for its adele ring and $\mathrm{GL}_2(\mathbb{A}_K)$ for `AdelicGL2 (𝓞 K) K`, and let $\mathcal{K} =$ `maximalCompactAt K ∅` be the subgroup of those $k \in \mathrm{GL}_2(\mathbb{A}_K)$ whose finite part lies in `finiteIntegralGL2 (𝓞 K) K`, whose archimedean component at every infinite place $w$ satisfies `IsRowIsometry` (unit determinant norm and preservation of $\|x\|^2+\|y\|^2$ by the row action), and whose finite component at every finite place is trivial. Let $\nu : \mathbb{A}_K^\times \to \mathbb{C}^\times$ be a group homomorphism whose associated $\mathbb{C}$-valued function is continuous, and let $\beta : \mathcal{K} \to \mathbb{C}$ be continuous, not identically zero, and covariant in the sense that $\nu(m_{11}) \cdot \beta(mk) = \beta(k)$ for every $m \in \mathcal{K}$ lying in `adelicBorel (𝓞 K) K` (lower-left entry zero) and every $k \in \mathcal{K}$, where $m_{11}$ denotes the second diagonal entry of $m$, viewed as an adelic unit via `borelDiagSnd`. Then there exists a continuous $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ satisfying `IsArchKFinite K f`, i.e. for each infinite place $w$ the right translates of $f$ under `archRowIsometrySubgroup K w` satisfy `RightTranslatesSpanFinite`, such that $f(mk) = \nu(m_{11}) \cdot f(k)$ for all $m, k \in \mathrm{GL}_2(\mathbb{A}_K)$ with trivial finite part and row-isometric archimedean components at all infinite places, $m$ lower-left zero, and such that $\int_{\mathcal{K}} f(k)\beta(k)\, d k \ne 0$ for the Haar measure `maximalCompactAtHaar K ∅`. The equivariance of $f$ is thus formulated through the conditions $\mathrm{glFin}\,m = \mathrm{glFin}\,k = 1$ and row-isometry at every infinite place rather than through membership in $\mathcal{K}$.
--
--   This is the non-degeneracy statement complementary to [`AutomorphicForm.eq_zero_of_continuous_of_forall_isArchKFinite_integral_maximalCompactAtHaar_mul_eq_zero`](thm.html#AutomorphicForm.eq_zero_of_continuous_of_forall_isArchKFinite_integral_maximalCompactAtHaar_mul_eq_zero): a continuous kernel on the archimedean maximal compact subgroup that is non-zero and covariant under its Borel part through $\nu$ admits an arch-finite test function of matching equivariance pairing non-trivially with it, the analytic input being density of $K_\infty$-finite functions. It is used in the Rankin–Selberg part of the development to select an archimedean datum for an induced section, in the two statements producing an arch-translate whose integral against a torus integral of a Whittaker coefficient is non-zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isArchKFinite_equivariant_integral_maximalCompactAtHaar_mul_ne_zero.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain

theorem AutomorphicForm.exists_isArchKFinite_equivariant_integral_maximalCompactAtHaar_mul_ne_zero
    (K : Type) [Field K] [NumberField K]
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
    (β : ↥(maximalCompactAt K ∅) → ℂ) (_hβ : Continuous β)
    (_hβν : ∀ (m : AdelicGL2 (𝓞 K) K) (hm : m ∈ adelicBorel (𝓞 K) K) (hmK : m ∈ maximalCompactAt K ∅)
      (k : ↥(maximalCompactAt K ∅)),
        ((ν (borelDiagSnd (⟨m, hm⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) * β (⟨m, hmK⟩ * k) = β k)
    (_hne : ∃ k₀ : ↥(maximalCompactAt K ∅), β k₀ ≠ 0) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ, Continuous f ∧ IsArchKFinite K f ∧
      (∀ (m k : AdelicGL2 (𝓞 K) K) (hm : m ∈ adelicBorel (𝓞 K) K),
        glFin (𝓞 K) K m = 1 → glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K m))) →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
          f (m * k) = ((ν (borelDiagSnd (⟨m, hm⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) * f k) ∧
      ∫ k, f (k : AdelicGL2 (𝓞 K) K) * β k ∂(maximalCompactAtHaar K ∅) ≠ 0 := by sorry
