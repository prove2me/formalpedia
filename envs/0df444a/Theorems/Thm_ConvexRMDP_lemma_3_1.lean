-- Prove2me | Theorems.Thm_ConvexRMDP_lemma_3_1
-- name    : ConvexRMDP.lemma_3_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:15:33.34901+00:00
-- url     : https://prove2.me/theorems/6a391c62-c388-46e7-ae99-3b0c6d37bde4
-- title:
--   Lemma 3.1 (contraction lemma): $g(v^\star) = \min\{g(v) \mid v \ge F(v)\} = \max\{g(v) \mid v \le F(v)\}$
-- statement:
--   Let $\mathcal S$ be a finite set, let $F : \mathbb R^{\mathcal S} \to \mathbb R^{\mathcal S}$ be monotone ($v \le v'$ componentwise implies $F(v) \le F(v')$) and a contraction for the $\ell_\infty$ norm, and let $v^\star$ be its fixed point. Let $g : \mathbb R^{\mathcal S} \to \mathbb R$ be component-wise non-decreasing. Then
--   $$
--   g(v^\star) = \min\{g(v) \mid v \ge F(v)\} = \max\{g(v) \mid v \le F(v)\},
--   $$
--   both optima being attained at $v^\star$. Moreover, if $g$ is component-wise increasing, then $v^\star$ is the unique solution of both optimization problems: every $v$ with $v \ge F(v)$ and $g(v) = g(v^\star)$, and every $v$ with $v \le F(v)$ and $g(v) = g(v^\star)$, equals $v^\star$.
--
--   The lemma turns the computation of a fixed point into an optimization problem; with a convex or concave choice of $F$ and $g$ it yields convex formulations, and it is the first step of the proof of Theorem 4.1.
--
--   **Formalization Note** The contraction is `ContractingWith K F` for some $K < 1$ in the sup metric of `S → ℝ`; component-wise non-decreasing is `Monotone g` and component-wise increasing is `StrictMono g`, both for the componentwise order.
--
--   Differences from the source:
--   - encoding: v⋆ the unique fixed-point of F → a hypothesis F vs = vs; reason: a contraction has exactly one fixed point (Banach), so the hypothesis identifies v⋆.
--   - encoding: g component-wise non-decreasing / increasing → Monotone g / StrictMono g for the componentwise order; reason: on a finite product the two notions coincide.
--   - encoding: ℝ^S with componentwise order and ℓ∞ norm → S → ℝ with the Pi order and the sup metric; reason: Lean convention; identical order and metric.
--   - encoding: g(v⋆) = min{…} = max{…}; v⋆ the unique solution → IsLeast / IsGreatest of the image sets; every feasible v with g v = g v⋆ equals v⋆; reason: same content, including attainment at v⋆.
-- source:
--   Grand-Clément & Petrik, On the Convex Formulations of Robust Markov Decision Processes, arXiv:2209.10187v2 (13 Dec 2023), Lemma 3.1, p.7 (proof in Appendix A.2, p.27)

import Mathlib

namespace ConvexRMDP

/-- **Lemma 3.1 (Contraction lemma)** (Grand-Clément & Petrik, arXiv:2209.10187v2, p.7; proof in
App. A.2, p.27). Let `F : ℝ^S → ℝ^S` be a monotone contraction, `g : ℝ^S → ℝ` component-wise
non-decreasing and `v⋆` the fixed point of `F`. Then
`g(v⋆) = min{g(v) | v ≥ F(v)} = max{g(v) | v ≤ F(v)}`, and if `g` is component-wise increasing,
`v⋆` is the unique solution of both problems.

**Formalization Note.** `ℝ^S` is `S → ℝ` with the componentwise order and the sup (`ℓ∞`) metric, so
"monotone contraction" is `Monotone F` and `ContractingWith K F` for some `K < 1`.
"Component-wise non-decreasing" is `Monotone g`; "component-wise increasing" is `StrictMono g` for
the componentwise order (equivalent for functions on a finite product). The fixed point of a
contraction is unique, so `F vs = vs` identifies `v⋆`. Each problem's value and attainment are
`IsLeast`/`IsGreatest`; uniqueness says every feasible point with the optimal value is `v⋆`. -/
theorem lemma_3_1 {S : Type*} [Fintype S] (F : (S → ℝ) → (S → ℝ)) (K : NNReal)
    (hF_mono : Monotone F) (hF_contr : ContractingWith K F)
    (g : (S → ℝ) → ℝ) (hg : Monotone g) (vs : S → ℝ) (hvs : F vs = vs) :
    IsLeast (g '' {v | F v ≤ v}) (g vs) ∧ IsGreatest (g '' {v | v ≤ F v}) (g vs) ∧
      (StrictMono g →
        (∀ v, F v ≤ v → g v = g vs → v = vs) ∧ (∀ v, v ≤ F v → g v = g vs → v = vs)) := by sorry

end ConvexRMDP
