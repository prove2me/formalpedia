-- Prove2me | Theorems.Thm_BSUMM_Det_lemma_2_5_part_1
-- name    : BSUMM.Det.lemma_2_5_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:56.700292+00:00
-- url     : https://prove2.me/theorems/76b0d790-2cdc-4ef8-b16b-902f0210ddc2
-- title:
--   Lemma 2.5(1), corrected per (2.19) — dual gap decrease Δ_d^{r+1} − Δ_d^r ≤ −α^r⟨Ex^r − q, Ex̄^{r+1} − q⟩
-- statement:
--   Consider problem (1.1) under Assumption A, with augmented dual function $d(y)=\min_{x\in X}L(x;y)$, dual optimal value $d^*$ and dual optimality gap $\Delta_d^r=d^*-d(y^r)$. Let $\{(x^r,y^r)\}$ be a run of BSUM-M (1.12) with stepsizes $\alpha^r$ and approximation functions $u_k$. Then for every $r\ge1$ and every $\bar x\in X(y^{r+1})$,
--   $$\Delta_d^{r+1}-\Delta_d^{r}\ \le\ -\alpha^{r}\,\langle Ex^{r}-q,\ E\bar x-q\rangle .$$
--
--   The dual step is a gradient ascent step on $d$ taken with the gradient direction $q-Ex^r$ at the current primal iterate; this inequality measures how much it improves the dual objective. Together with Lemma 2.3 it gives the primal gap estimate Lemma 2.6.
--
--   **Formalization Note** The printed (2.17) reads $\Delta_d^r-\Delta_d^{r-1}\le-\alpha^{r-1}(Ex^r-q)^T(E\bar x^r-q)$. Its proof (2.19) ends with $Ex^{r-1}$ in place of $Ex^r$, and the dual update $y^r-y^{r-1}=\alpha^{r-1}(q-Ex^{r-1})$ involves $x^{r-1}$, so $Ex^r$ is a typo; the statement here is the proved one, shifted by one index (the form used in the proof of Lemma 2.6). Any $\bar x\in X(y^{r+1})$ may be used, in particular the nearest point $\bar x^{r+1}$ to $x^{r+1}$; $E\bar x$ does not depend on the choice (Lemma 2.1). $d^*$ cancels in the difference.
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 13, Lemma 2.5 (1), (2.17), proof (2.19)

import Mathlib
import Definitions.Def_BSUMM_Det_Setting

namespace BSUMM.Det

open scoped InnerProductSpace

/-- Lemma 2.5, part 1 (Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 13), as
proved in (2.19) and used in Lemma 2.6 (the printed (2.17) has `Ex^r` where its proof has
`Ex^{r−1}`), stated with the index shifted by one: for every BSUM-M run, every `r ≥ 1` and every
`x̄ ∈ X(y^{r+1})`,
`Δ_d^{r+1} − Δ_d^r ≤ −α^r ⟨Ex^r − q, Ex̄ − q⟩`. -/
theorem lemma_2_5_part_1 {K : ℕ} {n : Fin K → ℕ} {m p : ℕ} (D : Data K n m p)
    (hA : D.AssumptionA) (u : (k : Fin K) → EuclideanSpace ℝ (Fin (n k)) → Xsp K n → ℝ)
    (α : ℕ → ℝ) (x : ℕ → Xsp K n) (y : ℕ → EuclideanSpace ℝ (Fin m)) (hrun : D.IsRun u α x y) :
    ∀ r, 1 ≤ r → ∀ xbar ∈ D.Xopt (y (r + 1)),
      D.dualGap (y (r + 1)) - D.dualGap (y r) ≤
        -(α r * ⟪D.Emul (x r) - D.q, D.Emul xbar - D.q⟫_ℝ) := by sorry

end BSUMM.Det
