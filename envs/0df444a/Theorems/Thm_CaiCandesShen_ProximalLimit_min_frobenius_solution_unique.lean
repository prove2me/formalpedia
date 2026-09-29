-- Prove2me | Theorems.Thm_CaiCandesShen_ProximalLimit_min_frobenius_solution_unique
-- name    : CaiCandesShen.ProximalLimit.min_frobenius_solution_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:26:27.949499+00:00
-- url     : https://prove2.me/theorems/8021cdb4-f0cf-485e-adb2-0b377f880698
-- title:
--   Proof of Theorem 3.1 — the minimum Frobenius norm solution $X_\infty$ of (1.6) is unique
-- statement:
--   Let $f_1,\dots,f_m:\mathbb R^{n_1\times n_2}\to\mathbb R$ be convex functions. If $X$ and $X'$ are both minimum Frobenius norm solutions (3.14) of the nuclear norm problem (1.6), that is, each solves
--   $$\text{minimize } \|X\|_* \quad\text{subject to } f_i(X)\le 0,\ i=1,\dots,m,$$
--   and has the smallest value of $\|\cdot\|_F^2$ among all solutions of (1.6), then
--   $$X = X' .$$
--
--   This is the uniqueness of $X_\infty$ that the last line of the proof of Theorem 3.1 invokes ("since $X_\infty$ is unique"), and it makes the definition (3.14) of $X_\infty$ unambiguous.
--
--   **Formalization Note** Convexity is `ConvexOn ℝ Set.univ (f i)` for each $i$. Existence of $X_\infty$ is not asserted; the statement is about any two matrices with the defining property.
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1967, proof of Theorem 3.1, last sentence ("since X_∞ is unique"); Eq. (3.14)

import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_CaiCandesShen_ProximalLimit_Problems
open Filter Topology

namespace CaiCandesShen.ProximalLimit

/-- Proof of Theorem 3.1, p. 1967, last line ("since X_∞ is unique"): when the `f_i` are convex,
the minimum Frobenius norm solution (3.14) of (1.6) is unique. -/
theorem min_frobenius_solution_unique {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (X X' : Mat n₁ n₂) (hX : IsMinFrobeniusSolution f X)
    (hX' : IsMinFrobeniusSolution f X') :
    X = X' := by sorry

end CaiCandesShen.ProximalLimit
