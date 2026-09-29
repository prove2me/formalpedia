-- Prove2me | Theorems.Thm_AutomorphicForm_eq_zero_of_continuous_of_forall_isArchKFinite_integral_maximalCompactAtHaar_mul_eq_zero
-- name    : AutomorphicForm.eq_zero_of_continuous_of_forall_isArchKFinite_integral_maximalCompactAtHaar_mul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/91d5153c-29dd-5838-8a10-e49c0f5ec7d4
-- title:
--   Continuous kernel orthogonal to all arch. K-finite functions vanishes
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal O_K$, and write $\mathrm{GL}_2(\mathbb A_K)$ for `AdelicGL2 (𝓞 K) K`, the general linear group of $2\times 2$ matrices over the adele ring of $K$. Consider the subgroup `maximalCompactAt K ∅`: its elements are those $k$ whose finite part $\mathrm{glFin}(k)$ lies in `finiteIntegralGL2 (𝓞 K) K` and whose archimedean component at each infinite place $w$ of $K$ is a row isometry, and which moreover lie, for every height-one prime $v$ of $\mathcal O_K$ (the complement of the empty set of primes), in the kernel of the map sending $k$ to the image of $\mathrm{glFin}(k)$ in $\mathrm{GL}_2$ of the $v$-adic completion; so the finite component is trivial at every finite place. Let $\beta$ be a continuous complex-valued function on this subgroup, and suppose that for every continuous $f : \mathrm{GL}_2(\mathbb A_K) \to \mathbb C$ which is archimedean $K$-finite, in the sense that for each infinite place $w$ the right translates of $f$ by the row-isometry subgroup `archRowIsometrySubgroup K w` span a finite-dimensional space (`RightTranslatesSpanFinite`), one has $\int f(k)\,\beta(k)\,d k = 0$, the integral being taken over the subgroup against `maximalCompactAtHaar K ∅`, the Haar measure `Measure.haarMeasure ⊤`. Then $\beta$ is identically zero, as an equality of functions, not merely almost everywhere.
--
--   This is the separation statement underlying the choice of archimedean $K$-finite test functions: the $K_\infty$-finite functions pair nontrivially with any nonzero continuous kernel on the archimedean maximal compact subgroup, by Stone–Weierstrass (equivalently Peter–Weyl) density. It is cited by [`AutomorphicForm.exists_isArchKFinite_equivariant_integral_maximalCompactAtHaar_mul_ne_zero`](thm.html#AutomorphicForm.exists_isArchKFinite_equivariant_integral_maximalCompactAtHaar_mul_ne_zero) and [`AutomorphicForm.exists_isArchKFinite_invariant_nonneg_integral_maximalCompactAtHaar_mul_ne_zero`](thm.html#AutomorphicForm.exists_isArchKFinite_invariant_nonneg_integral_maximalCompactAtHaar_mul_ne_zero), which produce $K$-finite functions with nonvanishing pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_zero_of_continuous_of_forall_isArchKFinite_integral_maximalCompactAtHaar_mul_eq_zero.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.eq_zero_of_continuous_of_forall_isArchKFinite_integral_maximalCompactAtHaar_mul_eq_zero
    (K : Type) [Field K] [NumberField K]
    (β : ↥(maximalCompactAt K ∅) → ℂ) (_hβ : Continuous β)
    (_h : ∀ f : AdelicGL2 (𝓞 K) K → ℂ, Continuous f → IsArchKFinite K f →
      ∫ k, f (k : AdelicGL2 (𝓞 K) K) * β k ∂(maximalCompactAtHaar K ∅) = 0) :
    β = 0 := by sorry
