-- Prove2me | Theorems.Thm_AffinePolicies_GeneralApprox_theorem_6
-- name    : AffinePolicies.GeneralApprox.theorem_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:25:56.13332+00:00
-- url     : https://prove2.me/theorems/5a698ddd-5f4d-4bc8-a79a-ab02b6c12354
-- title:
--   Theorem 6, PDF p. 35 — the optimal first stage for Π_Adapt(𝒰⁰) is a 4√m-approximation for Π_Adapt(𝒰)
-- statement:
--   Consider the two-stage problem $\Pi_{Adapt}(\mathcal U)$ of (1): $A\in\mathbb R^{m\times n_1}$ arbitrary, $B\in\mathbb R^{m\times n_2}$, $c\in\mathbb R^{n_1}_+$, $d\in\mathbb R^{n_2}_+$, and $\mathcal U\subseteq\mathbb R^m_+$ convex, compact and full-dimensional, with (1) feasible. Let $\mu_j=\max\{b_j:b\in\mathcal U\}$ and $\beta^j\in\arg\max\{b_j:b\in\mathcal U\}$ as in (38), let $u^1,\dots,u^K$ be a complete run of Algorithm $\mathcal A$ with output $\beta=u^1+\dots+u^K$, and let
--   $$\mathcal U^0=\operatorname{conv}\{2\sqrt m\cdot\beta^1,\dots,2\sqrt m\cdot\beta^m,\ 2\beta\}$$
--   be the set (66). Let $(\tilde x,\tilde y)$ be an optimal solution of $\Pi_{Adapt}(\mathcal U^0)$. Then for every $b\in\mathcal U$ there is $y\ge0$ with $A\tilde x+By\ge b$ and
--   $$c^T\tilde x+d^Ty\ \le\ 4\sqrt m\cdot z_{Adapt}(\mathcal U).$$
--   Equivalently, the solution that uses $\tilde x$ as first stage and $y(b)=\arg\min\{d^Ty: By\ge b-A\tilde x,\ y\ge0\}$ in each scenario has worst-case cost at most $4\sqrt m\cdot z_{Adapt}(\mathcal U)$.
--
--   This is the paper's $O(\sqrt m)$-approximation for the general case: without any sign condition on $A$, solving a problem over an $(m+1)$-point convex hull yields a first-stage decision within a factor $4\sqrt m$ of the fully adaptable optimum.
--
--   **Formalization Note** The page states the factor as $O(\sqrt m)$; the constant $4\sqrt m$ is the one its proof establishes (last display of PDF p. 39, via Lemma 13). The second stage is stated existentially: the minimum $\min\{d^Ty: By\ge b-A\tilde x, y\ge0\}$ is at most the bound exactly when some feasible $y$ achieves it, and this form avoids an argmax and the junk value of an infimum over an empty set. The statement holds for every run of Algorithm $\mathcal A$ and every choice of the maximizers $\beta^j$. The paper's "$\tilde x\in\mathbb R^n_+$" means $\mathbb R^{n_1}_+$; nonnegativity of $\tilde x$ is part of feasibility.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Theorem 6, PDF p. 35 (proof PDF p. 39)

import Mathlib
import Definitions.Def_AffinePolicies_GeneralApprox_Setting

namespace AffinePolicies.GeneralApprox

open Matrix

/-- Theorem 6 (PDF p. 35): let 𝒰⁰ be the set (66) built from the argmax points βʲ of (38) and a
run of Algorithm 𝒜, and let (x̃, ỹ) be an optimal solution of Π_Adapt(𝒰⁰). Then the first stage
x̃ is a 4√m-approximation for Π_Adapt(𝒰): for every b ∈ 𝒰 some second stage y ≥ 0 with
A x̃ + B y ≥ b has cᵀx̃ + dᵀy ≤ 4√m · z_Adapt(𝒰). No sign condition is imposed on A. -/
theorem theorem_6 {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ))
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (hUconv : Convex ℝ U) (hUcpt : IsCompact U) (hUfull : (interior U).Nonempty)
    (hfeas : ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ), AffinePolicies.Simplex.Feasible A B U x y)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (bstar : Fin m → Fin m → ℝ) (hbstar : ∀ j, bstar j ∈ U ∧ bstar j j = μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : AffinePolicies.SqrtBound.IsRun U μ K u)
    (xt : Fin n₁ → ℝ) (yt : (Fin m → ℝ) → Fin n₂ → ℝ)
    (hopt : AffinePolicies.Simplex.IsOptimalAdapt A B c d (U0 bstar u K) xt yt) :
    ∀ b ∈ U, ∃ y : Fin n₂ → ℝ, 0 ≤ y ∧ b ≤ A *ᵥ xt + B *ᵥ y ∧
      c ⬝ᵥ xt + d ⬝ᵥ y ≤ 4 * Real.sqrt m * AffinePolicies.Simplex.zAdapt A B c d U := by sorry

end AffinePolicies.GeneralApprox
