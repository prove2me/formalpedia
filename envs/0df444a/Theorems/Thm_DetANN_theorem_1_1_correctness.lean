-- Prove2me | Theorems.Thm_DetANN_theorem_1_1_correctness
-- name    : DetANN.theorem_1_1_correctness
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T17:41:54.060198+00:00
-- url     : https://prove2.me/theorems/4422449b-0438-49cd-b7cc-92be6ab40c27
-- title:
--   §7.4: correctness of the Theorem 1.1 data structure
-- statement:
--   There is $C_0^\ast>0$ such that the following holds for every $C_0\ge C_0^\ast$. Let $d,n,k\in\mathbb N$ with $d\le2^k$, let $P_1,\dots,P_n\in\mathbb R^d$ be distinct and $\varepsilon\in(0,1)$. Build the blocks and walk tuples of the definition `DetANN_Construction` for the zero-padded points in $\mathbb R^{2^k}$. Let $q\in\mathbb R^d$, and for each tuple $v$ let $x_v$ be one of the points such that the padded points satisfy the local guarantee (25) with $\alpha=1+\varepsilon/100$. Then
--
--   $$\min_v\|q-x_v\|\le(1+\varepsilon)\min_i\|q-P_i\|.$$
--
--   This is the correctness part of the proof of Theorem 1.1: if every local structure returns a $(1+\varepsilon/100)$-approximate neighbor in its projected space, the best returned point is a $(1+\varepsilon)$-approximate nearest neighbor.
--
--   **Formalization Note.** The statement holds for every power of two $2^k\ge d$, including $d'=2^{\lceil\log_2d\rceil}$; the assumption $d\le n$ of Theorem 1.1 matters only for the resource bounds. The minimum over $v$ is expressed as the existence of $v$ with $\|q-x_v\|\le(1+\varepsilon)\|q-P_i\|$ for every $i$.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), §7.4, proof of Theorem 1.1, p.19

import Mathlib
import Definitions.Def_DetANN_Construction
import Definitions.Def_DetANN_TupleFamily

namespace DetANN

/-- **§7.4, correctness of the Theorem 1.1 data structure.** Pad `P` with zeros to `ℝ^{2^k}`
(`d ≤ 2^k`), build the blocks of the greedy Theorem 3.2 construction (Sylvester matrix,
`τ = ε²/10⁶`) and the walk tuples of the Lemma 7.1 graph on `Fin (2^k)` with walk length
`⌈log_{1/θ₀}(200/ε)⌉`. If the points `x_v` satisfy the local guarantee with `α = 1 + ε/100`, then
one of them is a `(1 + ε)`-approximate nearest neighbor of `q`. -/
theorem theorem_1_1_correctness :
    ∃ C₀s : ℝ, 0 < C₀s ∧ ∀ C₀ : ℝ, C₀s ≤ C₀ → ∀ (d n k : ℕ), d ≤ 2 ^ k →
      ∀ P : Fin n → EuclideanSpace ℝ (Fin d), Function.Injective P →
        ∀ ε : ℝ, 0 < ε → ε < 1 →
          ∀ (q : EuclideanSpace ℝ (Fin d)) (x : Fin (2 ^ k) → Fin n),
            LocalGuarantee (annBlocks C₀ k P ε) (annTuples k ε) (paddedSet k P)
                (padVec (2 ^ k) q) (fun v => padVec (2 ^ k) (P (x v))) (1 + ε / 100) →
              ∃ v, ∀ i, ‖q - P (x v)‖ ≤ (1 + ε) * ‖q - P i‖ := by sorry

end DetANN
