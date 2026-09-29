-- Prove2me | Theorems.Thm_AutomorphicForm_exists_eq_sum_rightConv_conjInvariant_principalLevel_of_isFactorizableTestFn
-- name    : AutomorphicForm.exists_eq_sum_rightConv_conjInvariant_principalLevel_of_isFactorizableTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/fe3c354f-8ccc-5a1f-9c74-ec26116d8362
-- title:
--   Arthur's parametrix lemma for factorizable test functions on GL₂
-- statement:
--   Let $K$ be a number field, $\mathcal{O}_K$ its ring of integers, $N \neq 0$ an ideal of $\mathcal{O}_K$, and write $U$ for the subgroup $\mathrm{principalLevel}(N) \sqcap \mathrm{finiteAdelicGL2Subgroup}$ of $\mathrm{GL}_2(\mathbb{A}_K)$, the intersection of `principalLevel (𝓞 K) K N` (itself the intersection of `levelOne (𝓞 K) K N` with its image under conjugation by the Weyl element) with the kernel of `glArch`, i.e. the elements with trivial archimedean component. Let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be a factorizable test function: $f(g) = f_\infty(\mathrm{glArch}\,g)\, f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ compactly supported and of the form $\Phi \circ \mathrm{archEntries}$ for some $\Phi$ that is $C^\infty$ on the space of $2 \times 2$ matrices over the mixed space of $K$, and $f_{\mathrm{fin}}$ locally constant and compactly supported on $\mathrm{GL}_2$ of the finite adeles. Assume $f(xu) = f(x)$ for all $x$ and all $u \in U$. Then there are $n \in \mathbb{N}$ and families $f_k, g_k$ ($k < n$) of functions on $\mathrm{GL}_2(\mathbb{A}_K)$ such that each $f_k$ is again a factorizable test function; each $g_k$ is continuous, compactly supported, bi-invariant under $U$ (i.e. $g_k(ux) = g_k(x) = g_k(xu)$ for $u \in U$), invariant under conjugation by $\mathrm{rowIsometryInclAt₀}\,K\,w\,\kappa$ for every infinite place $w$ of $K$ and every $\kappa$ in the group `rowIsometrySubgroup₀ w.Completion` of row isometries of $\mathrm{GL}_2(K_w)$, and supported on elements $x$ whose finite component $\mathrm{glFin}\,x$ equals $\mathrm{glFin}\,u$ for some $u \in U$; and for all $x$, $f(x) = \sum_{k<n} \int_{\mathrm{GL}_2(\mathbb{A}_K)} f_k(xy)\, g_k(y^{-1})\, dy$, the integral being `rightConv` against the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$.
--
--   This is Arthur's smoothing (parametrix) lemma specialised to $\mathrm{GL}_2$ over a number field and to test functions invariant under right translation by the principal level $N$: right convolution by $f$ is decomposed into finitely many compositions of convolution by a kernel invariant under conjugation by the archimedean row-isometry groups with convolution by a factorizable test function. It is the input to the estimate for sums of twisted convolution operators over a fundamental domain, which in turn yields the absolute, locally uniform convergence needed for the spectral side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_eq_sum_rightConv_conjInvariant_principalLevel_of_isFactorizableTestFn.lean

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.exists_eq_sum_rightConv_conjInvariant_principalLevel_of_isFactorizableTestFn
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : IsFactorizableTestFn K f)
    (hfU : ∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K),
      ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, f (x * u) = f x) :
    ∃ (n : ℕ) (fs gs : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ),
      (∀ k, IsFactorizableTestFn K (fs k)) ∧
      (∀ k, Continuous (gs k) ∧ HasCompactSupport (gs k) ∧
        IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (gs k) ∧
        (∀ (w : InfinitePlace K) (κ : rowIsometrySubgroup₀ w.Completion)
            (x : GL (Fin 2) (AdeleRing (𝓞 K) K)),
          gs k (rowIsometryInclAt₀ K w κ * x * (rowIsometryInclAt₀ K w κ)⁻¹) = gs k x) ∧
        (∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K), gs k x ≠ 0 →
          ∃ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
            glFin (𝓞 K) K u = glFin (𝓞 K) K x)) ∧
      ∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K), f x = ∑ k, rightConv K (fs k) (fun y => gs k y⁻¹) x := by sorry
