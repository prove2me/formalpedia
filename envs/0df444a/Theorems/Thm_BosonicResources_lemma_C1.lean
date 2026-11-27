-- Prove2me | Theorems.Thm_BosonicResources_lemma_C1
-- name    : BosonicResources.lemma_C1
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T06:26:38.814923+00:00
-- url     : https://prove2.me/theorems/fff11dc0-d605-46dc-82df-2d8e61b71011
-- title:
--   Lemma C.1: a family of $2^{\Omega(n^2)}$ well-separated column-orthonormal matrices
-- statement:
--   For a real matrix $X$ let $\|X\|_F=\sqrt{\operatorname{Tr}(XX^{T})}$ denote the Frobenius norm.
--
--   There is a universal constant $c>0$ such that for every integer $n>9$, with $s=\lceil n/9\rceil$, there exist an integer $M\ge2^{c\,n^{2}}$ and real $n\times s$ matrices $U_1,\dots,U_M$ with orthonormal columns, $U_a^{T}U_a=I_s$ for every $a$, such that
--
--   $$
--   \big\|U_a^{T}U_b\big\|_F^{2}\ \le\ \frac{n}{18}\qquad\text{for all }a\neq b .
--   $$
--
--   This packing result is quoted from [ABDH+20, Lemma 6.4], where it serves lower bounds for learning classical Gaussian distributions. In the paper the matrices $U_a$ label the members of the hard ensembles of Gaussian states, whose covariance matrices are built from the rank-$s$ projectors $U_aU_a^{T}$; these ensembles are the ones behind the lower bounds of Theorems 1, 2, 3, 4 and S6.
--
--   **Formalization Note** "Orthogonal columns" in the printed statement means orthonormal columns: the paper uses $U_aU_a^{T}$ as an orthogonal projector of rank $s$ (Eqs. (S53), (S69)). $\|X\|_F^{2}$ is written $\operatorname{Tr}(XX^{T})$. $2^{\Omega(n^{2})}$ is read as $M\ge2^{c\,n^{2}}$ with a universal $c>0$ (a real power of $2$). The family is indexed by `Fin M`; distinctness of the matrices is not a separate clause (two equal members would violate the separation condition, since $\|U_a^{T}U_a\|_F^{2}=s>n/18$).
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, App. C.1, Lemma C.1; quoting [ABDH+20, Lemma 6.4] (Ashtiani, Ben-David, Harvey, Liaw, Mehrabian, Plan, Near-optimal sample complexity bounds for robust learning of Gaussian mixtures via compression schemes, J. ACM 2020)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Lemma C.1 (A large family of well-separated column-orthonormal matrices).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Lemma C.1 (App. C.1), quoting [ABDH+20, Lemma 6.4] (Ashtiani, Ben-David, Harvey, Liaw, Mehrabian, Plan,
*Near-optimal sample complexity bounds for robust learning of Gaussian mixtures via compression schemes*, J. ACM
2020): "Suppose n > 9. There exists M = 2^{Ω(n²)} n-by-⌈n/9⌉ matrices {U_a}_{a=1}^M with orthogonal columns and
satisfy ‖U_aᵀ U_b‖_F² ≤ n/18 for all distinct pairs a, b ∈ [M]."

There is a universal `c > 0` such that for every `n > 9`, with `s = ⌈n/9⌉`, there are `M ≥ 2^{c n²}` real `n × s`
matrices `U_1, …, U_M` with orthonormal columns (`U_aᵀ U_a = I_s`) and `‖U_aᵀ U_b‖_F² ≤ n/18` for all `a ≠ b`.

**Formalization Note.** "Orthogonal columns" means orthonormal columns: the paper uses `U_a U_aᵀ` as an orthogonal
projector of rank `s` (Eqs. (S53), (S69)). `‖X‖_F² = Tr(X Xᵀ)`. `2^{Ω(n²)}` is `M ≥ 2^{c n²}` with a universal
`c > 0`. -/
theorem lemma_C1 :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 9 < n →
      ∃ M : ℕ, (2 : ℝ) ^ (c * (n : ℝ) ^ 2) ≤ M ∧
        ∃ U : Fin M → Matrix (Fin n) (Fin ⌈(n : ℝ) / 9⌉₊) ℝ,
          (∀ a, (U a)ᵀ * U a = 1) ∧
          ∀ a b, a ≠ b → (((U a)ᵀ * U b) * ((U a)ᵀ * U b)ᵀ).trace ≤ (n : ℝ) / 18 := by sorry

end BosonicResources
