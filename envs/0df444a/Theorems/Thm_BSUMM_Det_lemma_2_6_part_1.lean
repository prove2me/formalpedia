-- Prove2me | Theorems.Thm_BSUMM_Det_lemma_2_6_part_1
-- name    : BSUMM.Det.lemma_2_6_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:58.984481+00:00
-- url     : https://prove2.me/theorems/10832ab9-ca9a-4fb6-a54b-ca67f6184586
-- title:
--   Lemma 2.6(1) — primal gap bound (2.20) for BSUM-M
-- statement:
--   Consider problem (1.1) under Assumption A, with approximation functions $u_k$ satisfying Assumption B. Write $\Delta_p^r=L(x^r;y^r)-d(y^r)$ for the primal optimality gap. Then there is a constant $\gamma>0$, depending only on the problem and the $u_k$, such that every run $\{(x^r,y^r)\}$ of BSUM-M (1.12) with stepsizes $\alpha^r$ satisfies, for each $r\ge1$ and every $\bar x\in X(y^{r+1})$,
--   $$\Delta_p^{r+1}-\Delta_p^r\ \le\ \alpha^r\|Ex^r-q\|^2-\gamma\|x^{r+1}-x^r\|^2-\alpha^r\langle Ex^r-q,\ E\bar x-q\rangle .$$
--
--   Combined with Lemma 2.5, this bounds the change of the potential $\Delta_p+\Delta_d$ along the iterations, which is the quantity the convergence proof of Theorem 2.1 tracks.
--
--   **Formalization Note** The paper writes "for some $\gamma$ independent of $y^r$"; $\gamma$ is Lemma 2.3's constant, and $\gamma>0$ is required here (with $\gamma\le0$ the bound would carry no information). $\gamma$ is quantified before the run. The page's $\bar x^{r+1}$ is any point of $X(y^{r+1})$; the right side depends on it only through $E\bar x$, which is constant on $X(y^{r+1})$.
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 14, Lemma 2.6 (1), (2.20)

import Mathlib
import Definitions.Def_BSUMM_Det_Setting

namespace BSUMM.Det

open scoped InnerProductSpace

/-- Lemma 2.6, part 1 (Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 14, (2.20)):
under Assumptions A and B there is `γ > 0`, independent of the run, such that every BSUM-M run
satisfies, for each `r ≥ 1` and every `x̄ ∈ X(y^{r+1})`,
`Δ_p^{r+1} − Δ_p^r ≤ α^r ‖Ex^r − q‖² − γ ‖x^{r+1} − x^r‖² − α^r ⟨Ex^r − q, Ex̄ − q⟩`. -/
theorem lemma_2_6_part_1 {K : ℕ} {n : Fin K → ℕ} {m p : ℕ} (D : Data K n m p)
    (hA : D.AssumptionA) (u : (k : Fin K) → EuclideanSpace ℝ (Fin (n k)) → Xsp K n → ℝ)
    (hB : D.AssumptionB u) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (α : ℕ → ℝ) (x : ℕ → Xsp K n) (y : ℕ → EuclideanSpace ℝ (Fin m)),
      D.IsRun u α x y → ∀ r, 1 ≤ r → ∀ xbar ∈ D.Xopt (y (r + 1)),
        D.primalGap (x (r + 1)) (y (r + 1)) - D.primalGap (x r) (y r) ≤
          α r * ‖D.Emul (x r) - D.q‖ ^ 2 - γ * ‖x (r + 1) - x r‖ ^ 2
            - α r * ⟪D.Emul (x r) - D.q, D.Emul xbar - D.q⟫_ℝ := by sorry

end BSUMM.Det
