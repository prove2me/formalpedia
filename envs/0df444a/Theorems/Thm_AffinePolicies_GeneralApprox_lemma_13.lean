-- Prove2me | Theorems.Thm_AffinePolicies_GeneralApprox_lemma_13
-- name    : AffinePolicies.GeneralApprox.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:25:30.929391+00:00
-- url     : https://prove2.me/theorems/e3bac026-d8c6-46b1-bb49-de058ef11409
-- title:
--   Lemma 13 (inequality), PDF p. 37 — z_Adapt(𝒰⁰) ≤ 4√m · z_Adapt(𝒰)
-- statement:
--   Consider the two-stage problem $\Pi_{Adapt}(\mathcal U)$ of (1) with $c\ge0$, $d\ge0$ and a convex, compact, full-dimensional uncertainty set $\mathcal U\subseteq\mathbb R^m_+$, and assume (1) is feasible. There is no sign condition on $A$. Let $\mu_j$ and $\beta^j$ be as in (38), let $u^1,\dots,u^K$ be a complete run of Algorithm $\mathcal A$ with output $\beta$, and let $\mathcal U^0=\operatorname{conv}\{2\sqrt m\beta^1,\dots,2\sqrt m\beta^m,2\beta\}$ be the set (66). Then $\Pi_{Adapt}(\mathcal U^0)$ has a feasible solution of finite worst-case cost, and
--   $$z_{Adapt}(\mathcal U^0)\ \le\ 4\sqrt m\cdot z_{Adapt}(\mathcal U).$$
--
--   Since $\mathcal U^0$ dominates $\mathcal U$ (Lemma 12), solving the problem over $\mathcal U^0$ costs at most a factor $4\sqrt m$ more than the original fully adaptable optimum; this is the cost half of Theorem 6.
--
--   **Formalization Note** The printed Lemma 13 also asserts $z_{Aff}(\mathcal U^0)=z_{Adapt}(\mathcal U^0)$, justified by "$\mathcal U^0$ is a simplex". The $m+1$ generators need not be affinely independent (for instance all $\beta^j$ coincide when one point of $\mathcal U$ maximizes every coordinate), so that equality is not stated here; Theorem 6 does not use it. The first conjunct, a feasible solution over $\mathcal U^0$ with a finite worst-case bound, prevents the value $z_{Adapt}(\mathcal U^0)$ from being the junk infimum of an empty set.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Lemma 13, PDF p. 37 (proof PDF pp. 37–39, (75)–(80))

import Mathlib
import Definitions.Def_AffinePolicies_GeneralApprox_Setting

namespace AffinePolicies.GeneralApprox

open Matrix

/-- Lemma 13 (PDF p. 37), the inequality: Π_Adapt(𝒰⁰) has a feasible solution with a finite
worst-case cost, and z_Adapt(𝒰⁰) ≤ 4√m · z_Adapt(𝒰). The printed equality
z_Aff(𝒰⁰) = z_Adapt(𝒰⁰) is not stated (see the Formalization Note). -/
theorem lemma_13 {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ) (B : Matrix (Fin m) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ))
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (hUconv : Convex ℝ U) (hUcpt : IsCompact U) (hUfull : (interior U).Nonempty)
    (hfeas : ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ), AffinePolicies.Simplex.Feasible A B U x y)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (bstar : Fin m → Fin m → ℝ) (hbstar : ∀ j, bstar j ∈ U ∧ bstar j j = μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : AffinePolicies.SqrtBound.IsRun U μ K u) :
    (∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ) (t : ℝ),
        AffinePolicies.Simplex.Feasible A B (U0 bstar u K) x y ∧ AffinePolicies.Simplex.CostLE c d (U0 bstar u K) x y t) ∧
      AffinePolicies.Simplex.zAdapt A B c d (U0 bstar u K) ≤ 4 * Real.sqrt m * AffinePolicies.Simplex.zAdapt A B c d U := by sorry

end AffinePolicies.GeneralApprox
