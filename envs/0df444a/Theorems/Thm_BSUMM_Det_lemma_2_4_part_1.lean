-- Prove2me | Theorems.Thm_BSUMM_Det_lemma_2_4_part_1
-- name    : BSUMM.Det.lemma_2_4_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:58.523891+00:00
-- url     : https://prove2.me/theorems/8a37d706-7d3c-4410-862e-3574c0702878
-- title:
--   Lemma 2.4(1), at y^{r+1} — the proximal gradient at x^r is O(‖x^{r+1} − x^r‖)
-- statement:
--   Consider problem (1.1) under Assumption A, with approximation functions $u_k$ satisfying Assumption B. For $(x,y)$ let $\tilde\nabla_xL(x;y)=x-p$, where $p=\arg\min_{u\in X}h(u)+\frac12\|x-\nabla_x(L(x;y)-h(x))-u\|^2$ is the proximal point of the gradient step for $h$ plus the indicator of $X$. Then there is a constant $\sigma>0$, depending only on the problem and the $u_k$, such that every run $\{(x^r,y^r)\}$ of BSUM-M (1.12) satisfies
--   $$\|\tilde\nabla_xL(x^r;y^{r+1})\|\ \le\ \sigma\,\|x^{r+1}-x^r\|\qquad\text{for all }r\ge1.$$
--
--   The proximal gradient vanishes exactly at minimizers of $L(\cdot;y)$ over $X$. The lemma says that when one sweep barely moves the primal iterate, the iterate is nearly optimal for the current augmented Lagrangian; with the error bound (2.4) it controls $\operatorname{dist}(x^r,X(y^{r+1}))$.
--
--   **Formalization Note** The printed (2.12) evaluates the proximal gradient at $y^r$. The primal step $x^{r+1}$ is computed with $y^{r+1}$, and with $y^r$ the bound fails already at $r=1$: for $K=1$, $\ell(t)=t^2/2$, $A=E=1$, $b=q=0$, $h=0$, $\rho=1$, $X=[-10,10]$, $u(v;x)=v^2$, $x^1=1$, $y^1=2+\alpha$ one gets $y^2=2$, $x^2=1$, while $\tilde\nabla L(x^1;y^1)=-\alpha\neq0$. The statement here uses $y^{r+1}$, the deterministic counterpart of the proved part (2), (2.13). The prox includes the constraint set $X$ (see the setting). $\sigma$ is quantified before the run ("independent of $y^r$").
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 11, Lemma 2.4 (1), (2.12)

import Mathlib
import Definitions.Def_BSUMM_Det_Setting

namespace BSUMM.Det

open scoped InnerProductSpace

/-- Lemma 2.4, part 1 (Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 11, (2.12)),
with the proximal gradient evaluated at `y^{r+1}` (the dual iterate with which `x^{r+1}` is
computed; as printed, with `y^r`, the bound fails at `r = 1`): under Assumptions A and B there is
`σ > 0`, independent of the run, such that every BSUM-M run satisfies
`‖∇̃L(x^r; y^{r+1})‖ ≤ σ ‖x^{r+1} − x^r‖` for all `r ≥ 1`, where `∇̃L(x; y) = x − p` with `p` the
proximal point of `x − ∇_x(L(x; y) − h(x))` for `h + ι_X`. -/
theorem lemma_2_4_part_1 {K : ℕ} {n : Fin K → ℕ} {m p : ℕ} (D : Data K n m p)
    (hA : D.AssumptionA) (u : (k : Fin K) → EuclideanSpace ℝ (Fin (n k)) → Xsp K n → ℝ)
    (hB : D.AssumptionB u) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ (α : ℕ → ℝ) (x : ℕ → Xsp K n) (y : ℕ → EuclideanSpace ℝ (Fin m)),
      D.IsRun u α x y → ∀ r, 1 ≤ r → ∀ pr : Xsp K n,
        D.IsProxPt (x r - D.gL (x r) (y (r + 1))) pr → ‖x r - pr‖ ≤ σ * ‖x (r + 1) - x r‖ := by sorry

end BSUMM.Det
