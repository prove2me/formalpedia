-- Prove2me | Theorems.Thm_ChenTeboullePMD_Rate_lemma_3_3_iii
-- name    : ChenTeboullePMD.Rate.lemma_3_3_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:53:26.060746+00:00
-- url     : https://prove2.me/theorems/44c74bbe-daf6-49ad-94a1-0709c53f16fc
-- title:
--   Lemma 3.3(iii), pp. 541–542 — weighted telescoping estimate
-- statement:
--   Under Lemma 3.2's standing assumptions, let $\sigma_n=\sum_{k=1}^n\lambda_k$. For every $n\ge1$ and $u\in C\cap\bar S$,
--   $$
--   \sigma_n\bigl(f(x^n)-f(u)\bigr)
--   \le D_\psi(u,x^0)-D_\psi(u,x^n)
--      -\sum_{k=1}^n\lambda_k^{-1}\sigma_k D_\psi(x^k,x^{k-1}).
--   $$
--
--   This is the weighted estimate that gives Theorem 3.4's rate after the nonnegative terms are removed.
--
--   **Formalization Note** The weights are exactly $\lambda_k^{-1}\sigma_k$; the sum uses a zero-based Lean range with $k+1$ as the paper index. The real inequality covers $u$ in the effective domain, where the page's extended objective is finite. The space is finite dimensional and the run predicate supplies existing zone-valued iterates.
-- source:
--   Chen & Teboulle, Convergence analysis of a proximal-like minimization algorithm using Bregman functions, SIAM J. Optim. 3 (1993), pp. 541–542, Lemma 3.3(iii)

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting
import Definitions.Def_ChenTeboullePMD_Rate_Setting

namespace ChenTeboullePMD.Rate

open BeckTeboulleMD.EMDA

/-- Lemma 3.3(iii), pp. 541–542. -/
theorem lemma_3_3_iii {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (ψ : E → ℝ) (hψ : IsBregmanFunction S ψ)
    (C : Set E) (hCne : C.Nonempty) (hCconv : Convex ℝ C)
    (f : E → ℝ) (hf : ConvexOn ℝ C f)
    (hlsc : LowerSemicontinuous (extendTop C f))
    (hri : intrinsicInterior ℝ C ⊆ S)
    (lam : ℕ → ℝ) (hlam : ∀ k, 1 ≤ k → 0 < lam k)
    (x : ℕ → E) (hrun : IsPMDRun S C ψ f lam x) :
    ∀ n, 1 ≤ n → ∀ u ∈ C, u ∈ closure S →
      sigma lam n * (f (x n) - f u) ≤
        bregman ψ u (x 0) - bregman ψ u (x n) -
          ∑ k ∈ Finset.range n,
            (lam (k + 1))⁻¹ * sigma lam (k + 1) *
              bregman ψ (x (k + 1)) (x k) := by sorry

end ChenTeboullePMD.Rate
