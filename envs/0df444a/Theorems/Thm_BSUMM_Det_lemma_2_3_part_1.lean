-- Prove2me | Theorems.Thm_BSUMM_Det_lemma_2_3_part_1
-- name    : BSUMM.Det.lemma_2_3_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:32:06.723209+00:00
-- url     : https://prove2.me/theorems/1db87c01-2dde-4bc4-bc4a-6d7818439a99
-- title:
--   Lemma 2.3(1) — one BSUM-M primal sweep decreases the augmented Lagrangian by γ‖x^r − x^{r+1}‖²
-- statement:
--   Consider problem (1.1) under Assumption A, with approximation functions $u_k$ satisfying Assumption B, and let $L$ be the augmented Lagrangian (1.8). Then there is a constant $\gamma>0$, depending only on the problem and the $u_k$, such that every run $\{(x^r,y^r)\}$ of BSUM-M (1.12), with any stepsizes, satisfies
--   $$L(x^r;y^{r+1})-L(x^{r+1};y^{r+1})\ \ge\ \gamma\,\|x^r-x^{r+1}\|^2\qquad\text{for all }r\ge1.$$
--
--   One full Gauss–Seidel sweep over the primal blocks, performed with the dual variable held at $y^{r+1}$, decreases the augmented Lagrangian by an amount proportional to the squared length of the step. This is the primal descent estimate behind Lemma 2.6.
--
--   **Formalization Note** The constant $\gamma$ is quantified before the run, matching "independent of $r$ and $y^{r+1}$". The paper's proof sets $\gamma=\min_k\gamma_k$; with B(d)'s modulus $\gamma_k/2$ the argument gives $\min_k\gamma_k/2$, so only the existence of some $\gamma>0$ is stated.
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 10, Lemma 2.3 (1), (2.7)

import Mathlib
import Definitions.Def_BSUMM_Det_Setting

namespace BSUMM.Det

open scoped InnerProductSpace

/-- Lemma 2.3, part 1 (Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 10, (2.7)):
under Assumptions A and B there is a constant `γ > 0`, independent of the iteration and of the
dual iterates, such that every BSUM-M run satisfies
`L(x^r; y^{r+1}) − L(x^{r+1}; y^{r+1}) ≥ γ ‖x^r − x^{r+1}‖²` for all `r ≥ 1`. -/
theorem lemma_2_3_part_1 {K : ℕ} {n : Fin K → ℕ} {m p : ℕ} (D : Data K n m p)
    (hA : D.AssumptionA) (u : (k : Fin K) → EuclideanSpace ℝ (Fin (n k)) → Xsp K n → ℝ)
    (hB : D.AssumptionB u) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (α : ℕ → ℝ) (x : ℕ → Xsp K n) (y : ℕ → EuclideanSpace ℝ (Fin m)),
      D.IsRun u α x y → ∀ r, 1 ≤ r →
        γ * ‖x r - x (r + 1)‖ ^ 2 ≤ D.Lag (x r) (y (r + 1)) - D.Lag (x (r + 1)) (y (r + 1)) := by sorry

end BSUMM.Det
