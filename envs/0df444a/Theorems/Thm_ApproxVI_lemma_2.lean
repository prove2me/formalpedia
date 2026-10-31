-- Prove2me | Theorems.Thm_ApproxVI_lemma_2
-- name    : ApproxVI.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:16:07.466466+00:00
-- url     : https://prove2.me/theorems/12829808-6538-498f-be6b-0105341d3c13
-- title:
--   Lemma 2 — the perturbed Bellman operator $\tilde T x = Tx + B^\epsilon$ is Marchaud
-- statement:
--   Let $\nu$ be positive weights, $0<\alpha<1$, and let $T:\mathbb R^d\to\mathbb R^d$ satisfy (AV1):
--
--   $$
--   \|Tx-Ty\|_\nu\le\alpha\|x-y\|_\nu\quad\text{for all }x,y.
--   $$
--
--   Let $\epsilon>0$. Then the set-valued map $\tilde Tx=Tx+B^\epsilon$ is a Marchaud map: its values are convex and compact, there is $K>0$ with $\|w\|<K(1+\|x\|)$ for all $x$ and all $w\in\tilde Tx$ (Euclidean norm), and it is upper-semicontinuous.
--
--   This is assumption (A1) of the paper's set-valued stochastic approximation framework, verified for AVI.
--
--   Differences from the source:
--   - generalization: T is the Bellman operator (3), contractive by (AV1) → T is any map ℝ^d → ℝ^d satisfying (AV1); reason: the argument uses only (AV1); the Bellman operator under (AV1) is an instance
--   - generalization: §5 assumes (AV1)–(AV5) throughout → only (AV1) is assumed; reason: the statement involves no errors, step sizes or noise; the other assumptions do not enter
--   - generalization: d ≥ 1 (used in the proof of Lemma 2) → any d ≥ 0; reason: for d = 0 the map is constant {0} and trivially Marchaud; the d ≥ 1 case is the source's
--   - reading: Marchaud (ii): for each x, sup_{w∈H(x)} ‖w‖ < K(1 + ‖x‖) for some K > 0 → one K > 0 for all x; reason: the quantifier order is ambiguous; this is the stronger reading, the one the proof of Lemma 2 establishes
--   - encoding: sup_{w∈H(x)} ‖w‖ < K(1 + ‖x‖) → ‖w‖ < K(1 + ‖x‖) for every w ∈ H(x); reason: equivalent on compact nonempty sets such as T̃x; avoids the junk real supremum of the empty set
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, Lemma 2, p.14

import Mathlib
import Definitions.Def_ApproxVI_Ttilde
import Definitions.Def_ApproxVI_IsMarchaud

namespace ApproxVI

/-- **Lemma 2**, Ramaswamy & Bhatnagar, *Analyzing Approximate Value Iteration Algorithms*,
arXiv:1709.04673v5, p.14: the set-valued map `T̃` given by `T̃x ↦ Tx + B^ε` is a Marchaud map.

The standing assumption (AV1) (§3.1, p.7) is a hypothesis: `T` is an `α`-contraction,
`0 < α < 1`, for the weighted max-norm `‖·‖_ν`, `νᵢ > 0`; and `ε > 0` (Lemma 1).

**Formalization Note** `T` is any map satisfying (AV1) (the page's `T` is the Bellman operator
(3)); the proof only uses (AV1). The proof's `d ≥ 1` is not assumed: for `d = 0` the claim
holds trivially. -/
theorem lemma_2 {d : ℕ} (ν : Fin d → ℝ) (hν : ∀ i, 0 < ν i) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (T : (Fin d → ℝ) → (Fin d → ℝ))
    (hT : ∀ x y, wNorm ν (T x - T y) ≤ α * wNorm ν (x - y)) (ε : ℝ) (hε : 0 < ε) :
    IsMarchaud (Ttilde ν T ε) := by sorry

end ApproxVI
