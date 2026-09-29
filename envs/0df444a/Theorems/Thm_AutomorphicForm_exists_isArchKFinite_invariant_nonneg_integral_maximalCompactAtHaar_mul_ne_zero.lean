-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isArchKFinite_invariant_nonneg_integral_maximalCompactAtHaar_mul_ne_zero
-- name    : AutomorphicForm.exists_isArchKFinite_invariant_nonneg_integral_maximalCompactAtHaar_mul_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/a2437ff2-a6b3-5dd6-9fc7-d1a09024eb05
-- title:
--   Non-negative K_∞-finite function pairing non-trivially with β
-- statement:
--   Let $K$ be a number field and let $\mathcal K =$ `maximalCompactAt K ∅` be the subgroup of $\mathrm{GL}_2(\mathbb A_K)$ consisting of those $k$ whose finite part lies in `finiteIntegralGL2` and is trivial at every finite place (the intersection of all kernels of the component maps `finComponent` composed with `glFin`), and whose archimedean component at each infinite place $w$ satisfies `IsRowIsometry`, i.e. has determinant of absolute value $1$ and acts on row vectors $(x,y)$ preserving $\|x\|^2+\|y\|^2$. Let $\beta : \mathcal K \to \mathbb C$ be continuous, invariant under left multiplication by elements $m$ of $\mathcal K$ lying in `adelicBorel` (lower-left adelic matrix entry zero), and not identically zero. Then there exists a continuous $f : \mathrm{GL}_2(\mathbb A_K) \to \mathbb C$ satisfying `IsArchKFinite K f`, i.e. at every infinite place $w$ the right translates of $f$ by `archRowIsometrySubgroup K w` span a finite-dimensional space, such that $f(mk) = f(k)$ whenever $m$ has vanishing lower-left entry and both $m$ and $k$ have trivial finite part and row-isometric archimedean components at all infinite places, such that $f(g)$ is real and $\ge 0$ for every $g$, and such that $\int_{\mathcal K} f(k)\beta(k)\,dk \neq 0$ for the Haar measure `maximalCompactAtHaar K ∅` on $\mathcal K$.
--
--   This is the non-degeneracy statement dual to the density of $K_\infty$-finite functions (a Peter–Weyl phenomenon): no non-zero continuous Borel-invariant kernel on the archimedean maximal compact subgroup is annihilated by all such functions, and one may moreover take the test function to be real-valued, non-negative and Borel-invariant. It is obtained from the vanishing criterion [`AutomorphicForm.eq_zero_of_continuous_of_forall_isArchKFinite_integral_maximalCompactAtHaar_mul_eq_zero`](thm.html#AutomorphicForm.eq_zero_of_continuous_of_forall_isArchKFinite_integral_maximalCompactAtHaar_mul_eq_zero), and is used in the Rankin–Selberg part of the argument to produce an archimedean test vector with a non-vanishing pairing against a Whittaker-type coefficient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isArchKFinite_invariant_nonneg_integral_maximalCompactAtHaar_mul_ne_zero.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain

theorem AutomorphicForm.exists_isArchKFinite_invariant_nonneg_integral_maximalCompactAtHaar_mul_ne_zero
    (K : Type) [Field K] [NumberField K]
    (β : ↥(maximalCompactAt K ∅) → ℂ) (_hβ : Continuous β)
    (_hβinv : ∀ (m : AdelicGL2 (𝓞 K) K) (_hm : m ∈ adelicBorel (𝓞 K) K) (hmK : m ∈ maximalCompactAt K ∅)
      (k : ↥(maximalCompactAt K ∅)), β (⟨m, hmK⟩ * k) = β k)
    (_hne : ∃ k₀ : ↥(maximalCompactAt K ∅), β k₀ ≠ 0) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ, Continuous f ∧ IsArchKFinite K f ∧
      (∀ (m k : AdelicGL2 (𝓞 K) K), m ∈ adelicBorel (𝓞 K) K →
        glFin (𝓞 K) K m = 1 → glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K m))) →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
          f (m * k) = f k) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, 0 ≤ (f g).re ∧ (f g).im = 0) ∧
      ∫ k, f (k : AdelicGL2 (𝓞 K) K) * β k ∂(maximalCompactAtHaar K ∅) ≠ 0 := by sorry
