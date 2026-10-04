-- Prove2me | Theorems.Thm_CookSensitivity_ChvatalRank_chvatalIter_subset_halfspace
-- name    : CookSensitivity.ChvatalRank.chvatalIter_subset_halfspace
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:06:17.472175+00:00
-- url     : https://prove2.me/theorems/02c6039d-177e-415a-aade-2a06fbb1f6a8
-- title:
--   Corollary 9 — after $(n^{2n}2^{n^3}+1)(\lfloor\max_P wx\rfloor-q)+1$ closures the cut $wx\le q$ holds
-- statement:
--   Let $P\subseteq\mathbb{Q}^n$ be a rational polyhedron with $P\cap\mathbb{Z}^n\ne\emptyset$, and let $w$ be an integral vector such that $q = \max\{wx : x\in P_I\}$ exists. Then $\max\{wx : x\in P\}$ exists, and
--
--   $$P^{(r)} \subseteq \{x : wx \le q\}, \qquad r = (n^{2n}2^{n^3}+1)\,\big(\lfloor \max\{wx : x \in P\}\rfloor - q\big) + 1.$$
--
--   Every valid inequality $wx \le q$ of the integer hull with integral $w$ is thus implied after a number of closure rounds controlled by the integrality gap of $w$; combined with Corollary 2 and Theorem 7 this gives Theorem 10.
--
--   **Formalization Note** $q$ is taken as an integer: any maximum of an integral $w$ over the convex hull of integral points is attained at an integral point, so this loses nothing. The existence of $\max\{wx : x \in P\}$ is proved in the paper and appears in the conclusion, not as a hypothesis. The difference $\lfloor\max\rfloor - q$ is nonnegative (since $P_I \subseteq P$) and is converted to $\mathbb{N}$ with `Int.toNat`.
-- source:
--   Cook, Gerards, Schrijver, Tardos, Sensitivity theorems in integer linear programming, Math. Programming 34 (1986), p. 260, Corollary 9

import Mathlib
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram
import Definitions.Def_CookSensitivity_ChvatalRank_ChvatalClosure

namespace CookSensitivity.ChvatalRank

open Matrix

theorem chvatalIter_subset_halfspace {n : ℕ} (P : Set (Fin n → ℚ))
    (hP : IsPolyhedron P) (hPZ : ∃ x ∈ P, IsIntegral x)
    (w : Fin n → ℤ) (q : ℤ)
    (hq : IsGreatest ((fun x => (fun i => (w i : ℚ)) ⬝ᵥ x) '' integerHull P) (q : ℚ)) :
    ∃ μ : ℚ, IsGreatest ((fun x => (fun i => (w i : ℚ)) ⬝ᵥ x) '' P) μ ∧
      chvatalIter ((n ^ (2 * n) * 2 ^ (n ^ 3) + 1) * (⌊μ⌋ - q).toNat + 1) P ⊆
        {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≤ (q : ℚ)} := by sorry

end CookSensitivity.ChvatalRank
