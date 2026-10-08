-- Prove2me | Theorems.Thm_AffinePolicies_SqrtBound_constructed_cost_le
-- name    : AffinePolicies.SqrtBound.constructed_cost_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:40:39.540245+00:00
-- url     : https://prove2.me/theorems/397a99f6-44c4-4ba9-b392-f4aa4885fa17
-- title:
--   Proof of Theorem 4, (56)–(59), PDF pp. 31–32 — the affine solution costs at most 3√m times the adaptive one
-- statement:
--   Assume $d\ge0$ and $\mathcal U\subseteq\mathbb R^m_+$. With $\mu$, $\beta^1,\dots,\beta^m$, a complete run $u^1,\dots,u^K$, $J_1$ of Algorithm $\mathcal A$, and a feasible solution $(x^*,y^*)$ of $\Pi_{Adapt}(\mathcal U)$ as in the feasibility milestone, let $\tilde x=3\sqrt m\,x^*$ and $\tilde y(b)=\sum_{j\in J_1}\frac{b_j}{\mu_j}y^*(\beta^j)+\hat y$ with $\hat y=\frac{2\sqrt m}{K}\sum_{k=1}^K y^*(u^k)$. If $t$ bounds the worst-case cost of $(x^*,y^*)$, that is $c^Tx^*+d^Ty^*(b)\le t$ for all $b\in\mathcal U$, then
--   $$c^T\tilde x+d^T\tilde y(b)\le 3\sqrt m\cdot t\qquad\text{for all } b\in\mathcal U .$$
--
--   Applied with $t$ approaching $z_{Adapt}(\mathcal U)$ this is the bound $c^T\tilde x+d^T\tilde y(b)\le3\sqrt m\cdot z_{Adapt}(\mathcal U)$ of the paper.
--
--   **Formalization Note** Stated for every feasible $(x^*,y^*)$ and every cost bound $t$, rather than for an optimal solution and $t=z_{Adapt}(\mathcal U)$; this avoids assuming attainment. Neither $A\ge0$ nor $c\ge0$ is needed and neither is assumed; $\mu>0$ is assumed.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Proof of Theorem 4, (56)–(59), PDF pp. 31–32

import Mathlib
import Definitions.Def_AffinePolicies_SqrtBound_Setting

open Matrix

namespace AffinePolicies.SqrtBound

theorem constructed_cost_le {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ))
    (hd : 0 ≤ d) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (μ : Fin m → ℝ) (hμ : ∀ j, IsGreatest ((fun b : Fin m → ℝ => b j) '' U) (μ j))
    (hμpos : ∀ j, 0 < μ j)
    (bstar : Fin m → Fin m → ℝ) (hbstar : ∀ j, bstar j ∈ U ∧ bstar j j = μ j)
    (K : ℕ) (u : ℕ → Fin m → ℝ) (hrun : IsRun U μ K u)
    (xs : Fin n₁ → ℝ) (ys : (Fin m → ℝ) → Fin n₂ → ℝ) (hfs : AffinePolicies.Simplex.Feasible A B U xs ys) :
    ∀ t : ℝ, AffinePolicies.Simplex.CostLE c d U xs ys t →
      AffinePolicies.Simplex.CostLE c d U ((3 * Real.sqrt m) • xs)
        (AffinePolicies.Simplex.affinePolicy (thmPolicyP ys bstar μ (J1 μ u K)) (thmPolicyq ys u K))
        (3 * Real.sqrt m * t) := by sorry

end AffinePolicies.SqrtBound
