-- Prove2me | Theorems.Thm_DetANN_theorem_3_2_greedy
-- name    : DetANN.theorem_3_2_greedy
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T17:41:30.314829+00:00
-- url     : https://prove2.me/theorems/d8dda7b8-36c2-4ab9-9a6c-b99fd2eed581
-- title:
--   Theorem 3.2: the greedy choice of signs gives $\Phi\le1/8$
-- statement:
--   There is $C_0^\ast>0$ such that the following holds for every $C_0\ge C_0^\ast$. Let $d\ge1$, let $h$ be a $d\times d$ matrix with entries $\pm1$ and $h^{\mathsf T}h=dI$, let $\tau\in(0,1)$, and let $P,\mathcal D\subseteq\mathbb R^d$ be finite with $0\notin\mathcal D$, $|\mathcal D|\ge1$, and $x-y\in\mathcal D$ or $y-x\in\mathcal D$ for all distinct $x,y\in P$. Put $p_0=\lceil\log_4(8|\mathcal D|d)\rceil$ and $L=\lceil C_0\tau^{-2}p_0\rceil$, and let $\xi^\ast$ be the greedy signs (definition `DetANN_SignChoice`) scored by the Lemma 6.2 expression. Then
--
--   $$\Phi(\xi^\ast)\le\tfrac18,\qquad \bigl|d\|A_jv\|^2-\|v\|^2\bigr|<\tau\|v\|^2\quad(v\in\mathcal D,\ j\le d),$$
--
--   and the blocks $A_1,\dots,A_d$ built from $\xi^\ast$ form a $\tau$-balanced block system for $P$.
--
--   The milestone `balanced_signs_exist` gives the existence of such signs. This theorem identifies the deterministic choice the algorithm makes: each sign takes the value that does not increase the conditional expectation of Lemma 6.2.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), proof of Theorem 3.2, p.16

import Mathlib
import Definitions.Def_DetANN_SignedBlocks
import Definitions.Def_DetANN_BalancedBlocks
import Definitions.Def_DetANN_SignChoice

namespace DetANN

/-- **Theorem 3.2, the deterministic construction.** Expose the `Ld` signs in the order
`(ℓ, r) ↦ ℓ·d + r` and fix each to the value that does not increase the conditional expectation of
Lemma 6.2 (`lemma62Expr`). With `p₀ = ⌈log₄(8Nd)⌉` and `L = ⌈C₀τ⁻²p₀⌉` for `C₀` large enough, the
resulting signs have `Φ ≤ 1/8`, are balanced on every difference in `𝒟`, and give a `τ`-balanced
block system for `P`. -/
theorem theorem_3_2_greedy :
    ∃ C₀s : ℝ, 0 < C₀s ∧ ∀ C₀ : ℝ, C₀s ≤ C₀ → ∀ d : ℕ, 1 ≤ d →
      ∀ h : Matrix (Fin d) (Fin d) ℝ, (∀ j r, h j r = 1 ∨ h j r = -1) →
        h.transpose * h = (d : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) →
        ∀ τ : ℝ, 0 < τ → τ < 1 →
          ∀ P D : Finset (EuclideanSpace ℝ (Fin d)), (∀ v ∈ D, v ≠ 0) →
            (∀ x ∈ P, ∀ y ∈ P, x ≠ y → x - y ∈ D ∨ y - x ∈ D) → 1 ≤ D.card →
            potential h (numReps C₀ τ (momentOrder D.card d))
                (greedySigns (lemma62Expr h (numReps C₀ τ (momentOrder D.card d)) τ
                  (momentOrder D.card d) D) (numReps C₀ τ (momentOrder D.card d) * d))
                τ (momentOrder D.card d) D ≤ 1 / 8 ∧
              (∀ v ∈ D, ∀ j : Fin d,
                |(d : ℝ) * ‖signedBlocks h (numReps C₀ τ (momentOrder D.card d))
                    (greedySigns (lemma62Expr h (numReps C₀ τ (momentOrder D.card d)) τ
                      (momentOrder D.card d) D) (numReps C₀ τ (momentOrder D.card d) * d)) j v‖ ^ 2
                    - ‖v‖ ^ 2| < τ * ‖v‖ ^ 2) ∧
              IsBalancedBlockSystem τ P (signedBlocks h (numReps C₀ τ (momentOrder D.card d))
                (greedySigns (lemma62Expr h (numReps C₀ τ (momentOrder D.card d)) τ
                  (momentOrder D.card d) D) (numReps C₀ τ (momentOrder D.card d) * d))) := by sorry

end DetANN
