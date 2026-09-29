-- Prove2me | Theorems.Thm_AutomorphicForm_exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate
-- name    : AutomorphicForm.exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/51ad9cf5-489b-533d-a907-e34e7f4a72a6
-- title:
--   Depth of lower unipotent invariance for translated level-N vectors
-- statement:
--   Let $K$ be a number field, $N$ a nonzero ideal of $\mathcal{O}_K$ and $S$ a finite set of finite places of $K$, i.e. of elements of the height one spectrum of $\mathcal{O}_K$. Let $x_0 : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be a function on `AdelicGL2 (𝓞 K) K`, the general linear group of rank $2$ over the adele ring, which is right invariant under the subgroup $\mathrm{levelOne}(N) \sqcap \mathrm{finiteAdelicGL2Subgroup}$: that is, $x_0(gk) = x_0(g)$ for all $g$ and all $k$ whose archimedean component is trivial (the image of $k$ under `glArch` is the identity) and whose finite component, the image under `glFin`, satisfies the predicate `IsLevelOneMatrix` for $N$ together with its inverse. Let $r \in \mathbb{N}$, let $A_1, \dots, A_r \in \mathrm{GL}_2(\mathbb{A}_K)$, let $c_1, \dots, c_r \in \mathbb{C}$, and let $x$ be the function $x(g) = \sum_{i} c_i\, x_0(g A_i)$. Then there is an integer $n > 0$ such that for every adele $\gamma$ whose archimedean component vanishes, whose component at each finite place outside $S$ vanishes, and which satisfies $\mathrm{v}(\gamma_v) \le \mathrm{ofAdd}(-n)$ for every $v \in S$, and for every $g \in \mathrm{GL}_2(\mathbb{A}_K)$, one has $x\bigl(g \cdot \mathrm{lowerUnipotentGL2}(\gamma)\bigr) = x(g)$, where $\mathrm{lowerUnipotentGL2}(\gamma)$ is the invertible matrix $\begin{pmatrix} 1 & 0 \\ \gamma & 1\end{pmatrix}$ with inverse $\begin{pmatrix} 1 & 0 \\ -\gamma & 1\end{pmatrix}$. No integrality is assumed of the translating matrices $A_i$.
--
--   This is the elementary uniformity statement fixing the depth of the ramified test data: a finite linear combination of right translates of a vector of level $N$ is invariant under lower unipotent elements that are deep enough at the finitely many finite places where they are supported. It is used in the construction of test data for the Rankin–Selberg integrals, in [`AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero`](thm.html#AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero) and [`AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_self_analyticOnNhd_re_pos`](thm.html#AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_self_analyticOnNhd_re_pos).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (_hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x₀ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hx₀lev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, x₀ (g * k) = x₀ g)
    (r : ℕ) (A : Fin r → AdelicGL2 (𝓞 K) K) (cs : Fin r → ℂ)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (_hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * A i)) :
    ∃ n : ℕ, 0 < n ∧ ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
      (∀ v ∈ S, Valued.v (γ.2 v) ≤
        ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
      x (g * lowerUnipotentGL2 γ) = x g := by sorry
