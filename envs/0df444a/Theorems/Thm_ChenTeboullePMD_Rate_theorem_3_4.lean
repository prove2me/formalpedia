-- Prove2me | Theorems.Thm_ChenTeboullePMD_Rate_theorem_3_4
-- name    : ChenTeboullePMD.Rate.theorem_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:53:54.387908+00:00
-- url     : https://prove2.me/theorems/7d819456-617c-42cf-a4a5-c1ca549faeed
-- title:
--   Theorem 3.4, p. 542 — PMD rate, value convergence, and convergence of iterates
-- statement:
--   Let $f$ be a proper lower semicontinuous convex extended-valued objective with effective domain $C$, let $\psi$ be a Bregman function with zone $S$ containing the relative interior of $C$, and let $(x^k)$ be a PMD run with positive steps $\lambda_k$. Set $\sigma_n=\sum_{k=1}^n\lambda_k$, let $f_* =\inf f\in[-\infty,\infty)$, and let $X_*$ be the set of minimizers. Then for every $n\ge1$ and $u\in C\cap\bar S$,
--   $$
--   f(x^n)-f(u)\le\sigma_n^{-1}D_\psi(u,x^0). \tag{20}
--   $$
--   If $\sigma_n\to+\infty$, then $f(x^n)\to f_*$, including when $f_*=-\infty$. For every $x^*\in X_*$ and $n\ge1$,
--   $$
--   f(x^n)-f(x^*)\le\sigma_n^{-1}D_\psi(x^*,x^0). \tag{21}
--   $$
--   If also $X_*\ne\varnothing$ and $\sigma_n\to+\infty$, the iterates converge to some point of $X_*$.
--
--   The rate and convergence statements are the paper's main result for proximal minimization with Bregman distances.
--
--   **Formalization Note** The space may be any finite-dimensional real normed space; derivatives are covectors. The total $\psi$ is used only on $\bar S$, and the PMD run predicate replaces the page's surjectivity assumption on $\nabla\psi$ by the resulting existence of zone-valued iterates. The real inequalities are restricted to finite comparison values $u\in C$. The bound $n\ge1$ ensures $\sigma_n>0$ and avoids evaluating $f(x^0)$ outside $C$. The infimum is in the extended reals so it may be $-\infty$; no lower bound on $f$ or prior existence of a minimizer is assumed. The printed $f^*$ in (21) is read as the previously defined $f_*$. The bound (21) follows for every minimizer without needing $\sigma_n\to+\infty$.
-- source:
--   Chen & Teboulle, Convergence analysis of a proximal-like minimization algorithm using Bregman functions, SIAM J. Optim. 3 (1993), p. 542, Theorem 3.4, (20)–(21)

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting
import Definitions.Def_ChenTeboullePMD_Rate_Setting

namespace ChenTeboullePMD.Rate

open BeckTeboulleMD.EMDA
open Filter
open scoped Topology

/-- Theorem 3.4 in full, p. 542: (20), convergence of values to the possibly
negative-infinite infimum, (21), and convergence of iterates when a minimizer exists. -/
theorem theorem_3_4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (ψ : E → ℝ) (hψ : IsBregmanFunction S ψ)
    (C : Set E) (hCne : C.Nonempty) (hCconv : Convex ℝ C)
    (f : E → ℝ) (hf : ConvexOn ℝ C f)
    (hlsc : LowerSemicontinuous (extendTop C f))
    (hri : intrinsicInterior ℝ C ⊆ S)
    (lam : ℕ → ℝ) (hlam : ∀ k, 1 ≤ k → 0 < lam k)
    (x : ℕ → E) (hrun : IsPMDRun S C ψ f lam x) :
    (∀ n, 1 ≤ n → ∀ u ∈ C, u ∈ closure S →
      f (x n) - f u ≤ (sigma lam n)⁻¹ * bregman ψ u (x 0)) ∧
    (Tendsto (sigma lam) atTop atTop →
      Tendsto (fun n => (f (x n) : EReal)) atTop
        (𝓝 (⨅ u ∈ C, (f u : EReal)))) ∧
    (∀ xs, (xs ∈ C ∧ ∀ v ∈ C, f xs ≤ f v) →
      ∀ n, 1 ≤ n →
        f (x n) - f xs ≤ (sigma lam n)⁻¹ * bregman ψ xs (x 0)) ∧
    (Tendsto (sigma lam) atTop atTop →
      (∃ xs, xs ∈ C ∧ ∀ v ∈ C, f xs ≤ f v) →
      ∃ z, (z ∈ C ∧ ∀ v ∈ C, f z ≤ f v) ∧
        Tendsto x atTop (𝓝 z)) := by sorry

end ChenTeboullePMD.Rate
