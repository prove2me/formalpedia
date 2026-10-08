-- Prove2me | Theorems.Thm_ChenTeboullePMD_Rate_lemma_3_2
-- name    : ChenTeboullePMD.Rate.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:39:32.640878+00:00
-- url     : https://prove2.me/theorems/2a427103-929d-4da4-8f73-876e43c0b177
-- title:
--   Lemma 3.2, pp. 540–541 — one-step Bregman descent inequality (13)
-- statement:
--   Let $f$ be a proper lower semicontinuous convex extended-valued objective with effective domain $C$, let $\psi$ be a Bregman function with zone $S$ containing the relative interior of $C$, and let $(x^k)$ be a PMD run with positive steps $\lambda_k$. For every $k\ge1$ and $u\in C\cap\bar S$,
--   $$
--   \lambda_k\bigl(f(x^k)-f(u)\bigr)
--   \le D_\psi(u,x^{k-1})-D_\psi(u,x^k)-D_\psi(x^k,x^{k-1}).
--   $$
--
--   This is the one-step estimate from which the weighted telescoping bound follows.
--
--   **Formalization Note** The ambient space is any finite-dimensional real normed space, with gradients represented by covectors. The extended objective is encoded by $C$ and real $f$ on $C$. The page's $u\in\bar S$ outside $C$ has $f(u)=+\infty$ and yields a trivial extended-valued comparison; the displayed real inequality covers its nontrivial domain. The PMD run predicate replaces the assumption that $\nabla\psi$ is onto, which the page uses to ensure the iterates exist.
-- source:
--   Chen & Teboulle, Convergence analysis of a proximal-like minimization algorithm using Bregman functions, SIAM J. Optim. 3 (1993), pp. 540–541, Lemma 3.2, (13)

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting
import Definitions.Def_ChenTeboullePMD_Rate_Setting

namespace ChenTeboullePMD.Rate

open BeckTeboulleMD.EMDA

/-- Lemma 3.2, display (13), pp. 540–541. -/
theorem lemma_3_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (ψ : E → ℝ) (hψ : IsBregmanFunction S ψ)
    (C : Set E) (hCne : C.Nonempty) (hCconv : Convex ℝ C)
    (f : E → ℝ) (hf : ConvexOn ℝ C f)
    (hlsc : LowerSemicontinuous (extendTop C f))
    (hri : intrinsicInterior ℝ C ⊆ S)
    (lam : ℕ → ℝ) (hlam : ∀ k, 1 ≤ k → 0 < lam k)
    (x : ℕ → E) (hrun : IsPMDRun S C ψ f lam x) :
    ∀ k : ℕ, ∀ u ∈ C, u ∈ closure S →
      lam (k + 1) * (f (x (k + 1)) - f u) ≤
        bregman ψ u (x k) - bregman ψ u (x (k + 1)) -
          bregman ψ (x (k + 1)) (x k) := by sorry

end ChenTeboullePMD.Rate
