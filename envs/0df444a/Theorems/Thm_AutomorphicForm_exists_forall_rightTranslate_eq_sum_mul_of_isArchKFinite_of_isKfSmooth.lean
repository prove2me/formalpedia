-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth
-- name    : AutomorphicForm.exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/4e65c820-5b9a-5983-9223-0234b817e61a
-- title:
--   Finite expansion of a K-finite smooth function on K
-- statement:
--   Let $F$ be a number field and let $\varphi$ be a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_F)$ (the group `AdelicGL2 (𝓞 F) F` of invertible $2\times 2$ matrices over the adele ring of $F$). Assume: `IsArchKFinite F φ`, i.e. at every infinite place $w$ of $F$ the finiteness condition `RightTranslatesSpanFinite` holds for $\varphi$ with respect to the subgroup `archRowIsometrySubgroup F w`; `IsKfSmooth F φ`, i.e. the stabiliser of $\varphi$, viewed as an element of `RightTranslationFn`, under right translation by `finiteAdelicGL2Subgroup F` (the kernel of the archimedean projection `glArch`) is an open subgroup; and $\varphi$ is continuous. Write $K$ for the set of $k\in\mathrm{GL}_2(\mathbb{A}_F)$ whose finite component `glFin (𝓞 F) F k` lies in `finiteIntegralGL2 (𝓞 F) F` (i.e. both it and its inverse satisfy `IsLevelZeroMatrix` at level $\top$) and whose archimedean component at each infinite place $w$, `archComponent F w (glArch (𝓞 F) F k)`, is a row isometry in the sense of `IsRowIsometry`: its determinant has norm $1$ and $(x,y)\mapsto (xk_{00}+yk_{10},\,xk_{01}+yk_{11})$ preserves $\|x\|^2+\|y\|^2$. Then there are $m\in\mathbb{N}$ and families $e_j,a_j\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ ($j\in\mathrm{Fin}\,m$) such that each $e_j$ is a finite linear combination $e_j(x)=\sum_i c_i\,\varphi(xk_i)$ with all $k_i\in K$, and each $e_j$ is again arch-$K$-finite and $K_f$-smooth; each $a_j$ is continuous on $K$; and $\varphi(xk)=\sum_j a_j(k)\,e_j(x)$ for every $k\in K$ and every $x\in\mathrm{GL}_2(\mathbb{A}_F)$.
--
--   This is the standard matrix-coefficient expansion of a continuous, $K_\infty$-finite, $K_f$-smooth function on $\mathrm{GL}_2(\mathbb{A}_F)$: its right $K$-translates lie in a finite-dimensional space spanned by translates of $\varphi$ itself, with coefficient functions continuous on $K$. It is used as the single-function input to the analytic continuation arguments for Weyl intertwining integrals, induced sections and Whittaker coefficients of Bruhat–Eisenstein series, where uniformity of the $K_\infty$-types and of the level is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth.lean

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth
    (F : Type) [Field F] [NumberField F] (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (_hφK : IsArchKFinite F φ) (_hφf : IsKfSmooth F φ) (_hφc : Continuous φ) :
    ∃ (m : ℕ) (e : Fin m → AdelicGL2 (𝓞 F) F → ℂ) (a : Fin m → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ j, (∃ (n : ℕ) (c : Fin n → ℂ) (k : Fin n → AdelicGL2 (𝓞 F) F),
          (∀ i, glFin (𝓞 F) F (k i) ∈ finiteIntegralGL2 (𝓞 F) F ∧
            ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F (k i)))) ∧
          e j = fun x => ∑ i, c i * φ (x * k i)) ∧
        IsArchKFinite F (e j) ∧ IsKfSmooth F (e j)) ∧
      (∀ j, ContinuousOn (a j) {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))}) ∧
      ∀ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        ∀ x : AdelicGL2 (𝓞 F) F, φ (x * k) = ∑ j, a j k * e j x := by sorry
