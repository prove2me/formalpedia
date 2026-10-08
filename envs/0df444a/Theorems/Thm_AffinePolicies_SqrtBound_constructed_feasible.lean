-- Prove2me | Theorems.Thm_AffinePolicies_SqrtBound_constructed_feasible
-- name    : AffinePolicies.SqrtBound.constructed_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:40:20.321479+00:00
-- url     : https://prove2.me/theorems/73c0e2f0-78d5-4f0e-9a13-94367e5deeae
-- title:
--   Proof of Theorem 4, (48)–(55), PDF pp. 30–31 — the affine solution x̃ = 3√m x*, ỹ(b) is feasible
-- statement:
--   Assume $A\ge0$ and $\mathcal U\subseteq\mathbb R^m_+$. Let $\mu_j=\max\{b_j:b\in\mathcal U\}>0$, let $\beta^j\in\mathcal U$ satisfy $\beta^j_j=\mu_j$, and take any complete run of Algorithm $\mathcal A$ with $K$ iterations, choices $u^1,\dots,u^K$ and final index set $J_1$. Let $(x^*,y^*)$ be any feasible solution of $\Pi_{Adapt}(\mathcal U)$. Define
--   $$\hat y=\frac{2\sqrt m}{K}\sum_{k=1}^K y^*(u^k),\qquad \tilde x=3\sqrt m\,x^*,\qquad \tilde y(b)=\sum_{j\in J_1}\frac{1}{\mu_j}\,y^*(\beta^j)\,b_j+\hat y .$$
--   Then $(\tilde x,\tilde y)$ is feasible for $\Pi_{Adapt}(\mathcal U)$: $\tilde x\ge0$ and, for every $b\in\mathcal U$, $\tilde y(b)\ge0$ and $A\tilde x+B\tilde y(b)\ge b$.
--
--   This is the first half of the proof of Theorem 4; $\tilde y$ is an affine policy.
--
--   **Formalization Note** The paper starts from an optimal $(x^*,y^*)$; the statement is made for every feasible one, which is stronger and avoids assuming that an optimum is attained. When $K=0$, $\hat y=0$ (the empty sum). Only $A\ge0$ and $\mathcal U\subseteq\mathbb R^m_+$ of the standing assumptions are used; $\mu>0$ is assumed (it follows from full-dimensionality, see the milestone on (38)).
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Proof of Theorem 4, (48)–(55), PDF pp. 30–31

import Mathlib
import Definitions.Def_AffinePolicies_SqrtBound_Setting

open Matrix

namespace AffinePolicies.SqrtBound

theorem constructed_feasible {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (U : Set (Fin m → ℝ))
    (hA : ∀ i j, 0 ≤ A i j) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (hμpos : ∀ j, 0 < μ j)
    (bstar : Fin m → Fin m → ℝ) (hbstar : ∀ j, bstar j ∈ U ∧ bstar j j = μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : IsRun U μ K u)
    (xs : Fin n₁ → ℝ) (ys : (Fin m → ℝ) → Fin n₂ → ℝ) (hfs : AffinePolicies.Simplex.Feasible A B U xs ys) :
    AffinePolicies.Simplex.Feasible A B U ((3 * Real.sqrt m) • xs)
      (AffinePolicies.Simplex.affinePolicy (thmPolicyP ys bstar μ (J1 μ u K)) (thmPolicyq ys u K)) := by sorry

end AffinePolicies.SqrtBound
