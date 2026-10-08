-- Prove2me | Theorems.Thm_ExtensionComplexity_TSP_valid_inequality_nonneg_combination
-- name    : ExtensionComplexity.TSP.valid_inequality_nonneg_combination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:47:40.212862+00:00
-- url     : https://prove2.me/theorems/54ca7676-0b08-4daa-9ef3-c8c876b3ba14
-- title:
--   Lemma 2 — valid inequalities of a polyhedron with a bounded nonconstant direction are nonnegative combinations
-- statement:
--   Let $A\in\mathbb R^{m\times d}$, $b\in\mathbb R^m$ and $P=\{x\in\mathbb R^d : Ax\le b\}$, a possibly unbounded polyhedron. Suppose some direction $u\in\mathbb R^d$ satisfies
--
--   $$-\infty<\min\{u^\top x : x\in P\}<\max\{u^\top x : x\in P\}<+\infty,$$
--
--   and let $c^\top x\le\delta$ be valid for $P$ (satisfied by every point of $P$). **Lemma 2**: there are nonnegative multipliers $\lambda\in\mathbb R^m$ with
--
--   $$\lambda^\top A=c^\top\qquad\text{and}\qquad\lambda^\top b=\delta,$$
--
--   that is, $c^\top x\le\delta$ is a nonnegative combination of the rows of $Ax\le b$, with equality in the right-hand side.
--
--   Ordinary Farkas gives $\lambda^\top b\le\delta$; the hypothesis on $u$ is what upgrades it to equality, and this is what the proof of Theorem 3 needs to show that rows of a slack matrix for redundant inequalities are nonnegative combinations of the others.
--
--   **Formalization Note** The page prints "$\lambda\in\mathbb R^d$"; since $A$ has $m$ rows, $\lambda\in\mathbb R^m$, which is what is stated. The minimum and maximum are required to exist (`IsLeast`/`IsGreatest` of $\{u^\top x : x\in P\}$), which is the meaning of the finite $\min$/$\max$. The lemma's "In particular" sentence (polytopes of dimension at least $1$, and unbounded polyhedra projecting onto them) is not part of this statement.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, pp. 17:9-17:10, Lemma 2

import Mathlib

open Matrix

namespace ExtensionComplexity.TSP

/-- **Lemma 2** (Fiorini et al., J. ACM 62(2) (2015), Art. 17, pp. 17:9–17:10): let
`P = {x ∈ ℝ^d | Ax ≤ b}` be a (possibly unbounded) polyhedron admitting a direction `u` such that
`min{uᵀx | x ∈ P}` and `max{uᵀx | x ∈ P}` are finite (attained) and the minimum is strictly less
than the maximum, and let `cᵀx ≤ δ` be valid for `P`. Then there are nonnegative multipliers
`λ ∈ ℝ^m` (the page prints `ℝ^d`; `A` has `m` rows) with `λᵀA = cᵀ` and `λᵀb = δ`. -/
theorem valid_inequality_nonneg_combination {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ)
    (b : Fin m → ℝ) (P : Set (Fin d → ℝ)) (hP : P = {x | A *ᵥ x ≤ b})
    (u : Fin d → ℝ) (lo hi : ℝ) (hlo : IsLeast ((fun x => u ⬝ᵥ x) '' P) lo)
    (hhi : IsGreatest ((fun x => u ⬝ᵥ x) '' P) hi) (hlohi : lo < hi)
    (c : Fin d → ℝ) (δ : ℝ) (hvalid : ∀ x ∈ P, c ⬝ᵥ x ≤ δ) :
    ∃ lam : Fin m → ℝ, 0 ≤ lam ∧ lam ᵥ* A = c ∧ lam ⬝ᵥ b = δ := by sorry

end ExtensionComplexity.TSP
