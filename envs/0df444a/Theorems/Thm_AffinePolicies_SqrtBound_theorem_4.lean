-- Prove2me | Theorems.Thm_AffinePolicies_SqrtBound_theorem_4
-- name    : AffinePolicies.SqrtBound.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:40:44.575737+00:00
-- url     : https://prove2.me/theorems/8c660a2b-3870-4668-940f-8a6f5e3bd0fd
-- title:
--   Theorem 4, PDF p. 26 — if A ≥ 0, then z_Aff(𝒰) ≤ 3√m · z_Adapt(𝒰)
-- statement:
--   Consider the two-stage adaptive problem $\Pi_{Adapt}(\mathcal U)$ of (1): minimize $c^Tx+\max_{b\in\mathcal U}d^Ty(b)$ subject to $Ax+By(b)\ge b$ for all $b\in\mathcal U$ and $x,y(b)\ge0$, where $c\in\mathbb R^{n_1}_+$, $d\in\mathbb R^{n_2}_+$, and the problem is feasible. Suppose the uncertainty set $\mathcal U\subseteq\mathbb R^m_+$ is convex, compact and full-dimensional and that $A\ge0$ entrywise. Then $\Pi_{Adapt}(\mathcal U)$ has a feasible solution with an affine second stage $y(b)=Pb+q$, and
--   $$z_{Aff}(\mathcal U)\le 3\sqrt m\cdot z_{Adapt}(\mathcal U),$$
--   that is, the worst-case cost of an optimal affine policy is at most $3\sqrt m$ times the worst-case cost of an optimal fully adaptable solution.
--
--   Together with the $\Omega(m^{1/2-\delta})$ lower bound of Theorem 3, this shows that the $O(\sqrt m)$ approximation factor of affine policies is tight up to a constant factor when $A\ge0$.
--
--   **Formalization Note** $z_{Adapt}$ and $z_{Aff}$ are infima of worst-case cost bounds over feasible solutions (with arbitrary, respectively affine, second stage). The existence of a feasible affine solution is part of the conclusion: without it $z_{Aff}$ would be the junk value $\inf\emptyset=0$ and the inequality would hold trivially.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Theorem 4, PDF p. 26

import Mathlib
import Definitions.Def_AffinePolicies_SqrtBound_Setting

open Matrix

namespace AffinePolicies.SqrtBound

theorem theorem_4 {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin m → ℝ))
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hUnn : ∀ b ∈ U, 0 ≤ b)
    (hUconv : Convex ℝ U) (hUcpt : IsCompact U) (hUfull : (interior U).Nonempty)
    (hfeas : ∃ (x : Fin n₁ → ℝ) (y : (Fin m → ℝ) → Fin n₂ → ℝ), AffinePolicies.Simplex.Feasible A B U x y)
    (hA : ∀ i j, 0 ≤ A i j) :
    (∃ (x : Fin n₁ → ℝ) (P : Matrix (Fin n₂) (Fin m) ℝ) (q : Fin n₂ → ℝ),
        AffinePolicies.Simplex.Feasible A B U x (AffinePolicies.Simplex.affinePolicy P q)) ∧
      AffinePolicies.Simplex.zAff A B c d U ≤ 3 * Real.sqrt m * AffinePolicies.Simplex.zAdapt A B c d U := by sorry

end AffinePolicies.SqrtBound
