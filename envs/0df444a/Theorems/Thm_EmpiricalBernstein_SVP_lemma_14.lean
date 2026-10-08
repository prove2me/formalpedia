-- Prove2me | Theorems.Thm_EmpiricalBernstein_SVP_lemma_14
-- name    : EmpiricalBernstein.SVP.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:49.968608+00:00
-- url     : https://prove2.me/theorems/fc71eef1-4050-4f1f-84b3-03ceafb4e881
-- title:
--   Lemma 14 — $\Pr_\sigma\{\Phi(f(\sigma,x,x'),t) > \Psi(f(-\sigma,x,x'),t)\} \le 5e^{-t}$
-- statement:
--   Let $n \ge 2$, let $f : \mathcal X \to [0,1]$, let $(x, x') \in \mathcal X^{2n}$ be fixed and let $t \ge 0$. Then
--
--   $$
--   \Pr_\sigma\Big\{ \Phi\big(f(\sigma,x,x'), t\big) > \Psi\big(f(-\sigma,x,x'), t\big) \Big\} \le 5 e^{-t},
--   $$
--
--   where $\sigma$ is uniformly distributed on $\{-1,1\}^n$, $(\sigma,x,x')$ is the swapped vector and $f(y) = (f(y_1),\dots,f(y_n))$.
--
--   This is where the concentration results of Section 2 (Theorems 10 and 11 and Bennett's inequality, for independent non-identical variables) enter the proof of the uniform bound, Theorem 6.
--
--   **Formalization Note** $\Pr_\sigma$ is the proportion of the $2^n$ sign vectors `σ : Fin n → Bool` satisfying the event. **Added hypotheses**: $n\ge2$ (at $n=1$ Lean's $1/(n-1) = 0$ collapses $\Phi$ and $\Psi$ to the coordinate itself, and the probability is $1/2$ whenever $f(x_1)\ne f(x'_1)$, exceeding $5e^{-t}$ for large $t$); $t \ge 0$, the domain $\mathbb R_+$ on which the paper defines $\Phi,\Psi$ (for $t \le 0$ the bound is $\ge 5$ anyway).
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, Lemma 14, p. 5

import Mathlib
import Definitions.Def_EmpiricalBernstein_SVP_PhiPsi
import Definitions.Def_EmpiricalBernstein_SVP_swap

namespace EmpiricalBernstein.SVP

/-- Lemma 14 (arXiv:0907.3740v1, p. 5): `Pr_σ` is the proportion of the `2^n` sign vectors `σ`;
`f(σ, x, x′)` is the vector `(f((σ, x, x′)_i))_i`; `n ≥ 2`, `t ≥ 0`. -/
theorem lemma_14 {𝒳 : Type*} {n : ℕ} (hn : 2 ≤ n) (f : 𝒳 → ℝ)
    (hf : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1) (x x' : Fin n → 𝒳) (t : ℝ) (ht : 0 ≤ t) :
    ((Finset.univ.filter (fun σ : Fin n → Bool =>
        Phi (fun i => f (swap σ x x' i)) t
          > Psi (fun i => f (swap (fun j => !σ j) x x' i)) t)).card : ℝ) / (2 : ℝ) ^ n
      ≤ 5 * Real.exp (-t) := by sorry

end EmpiricalBernstein.SVP
