-- Prove2me | Theorems.Thm_AffinePolicies_GeneralApprox_dominated_cost_le
-- name    : AffinePolicies.GeneralApprox.dominated_cost_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:25:52.799927+00:00
-- url     : https://prove2.me/theorems/c914a5dd-9cb8-4cc4-a7c0-e45da85bd9ce
-- title:
--   Theorem 6, proof, PDF p. 39 — an optimal first stage over a dominating set serves dominated scenarios at cost ≤ z_Adapt
-- statement:
--   Let $A,B,c,d$ be the data of the two-stage problem (1), and let $V,W\subseteq\mathbb R^m$ be two scenario sets such that $V$ dominates $W$: for every $b\in W$ there is $b'\in V$ with $b\le b'$. Let $(\tilde x,\tilde y)$ be an optimal solution of $\Pi_{Adapt}(V)$ whose worst-case cost over $V$ is finite. Then for every $b\in W$ there is a second-stage decision $y\ge0$ with
--   $$A\tilde x+By\ge b\qquad\text{and}\qquad c^T\tilde x+d^Ty\ \le\ z_{Adapt}(V).$$
--
--   This is the claim in the proof of Theorem 6 that the first stage $\tilde x$, completed by $\bar y(b)=\tilde y(b')$, has worst-case cost over $\mathcal U$ at most $z_{Adapt}(\mathcal U^0)$; here it is stated for an arbitrary dominating set.
--
--   **Formalization Note** The paper applies the claim with $V=\mathcal U^0$ and $W=\mathcal U$; the general form is the same argument. The hypothesis that the optimal solution has some finite worst-case bound is part of what "optimal solution" means on the page; without it the value would be the junk infimum of an empty set.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Theorem 6, proof, PDF p. 39

import Mathlib
import Definitions.Def_AffinePolicies_GeneralApprox_Setting

namespace AffinePolicies.GeneralApprox

open Matrix

/-- Proof of Theorem 6 (PDF p. 39), the claim that the solution is served at cost at most
z_Adapt(𝒰⁰): if every scenario of W is dominated by a scenario of V and (x̃, ỹ) is an optimal
solution of Π_Adapt(V) with a finite worst-case cost, then x̃ admits, for every b ∈ W, a feasible
second stage of total cost at most z_Adapt(V). -/
theorem dominated_cost_le {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ)
    (V W : Set (Fin m → ℝ)) (hdom : ∀ b ∈ W, ∃ b' ∈ V, b ≤ b')
    (xt : Fin n₁ → ℝ) (yt : (Fin m → ℝ) → Fin n₂ → ℝ)
    (hopt : AffinePolicies.Simplex.IsOptimalAdapt A B c d V xt yt) (hfin : ∃ t : ℝ, AffinePolicies.Simplex.CostLE c d V xt yt t) :
    ∀ b ∈ W, ∃ y : Fin n₂ → ℝ, 0 ≤ y ∧ b ≤ A *ᵥ xt + B *ᵥ y ∧
      c ⬝ᵥ xt + d ⬝ᵥ y ≤ AffinePolicies.Simplex.zAdapt A B c d V := by sorry

end AffinePolicies.GeneralApprox
