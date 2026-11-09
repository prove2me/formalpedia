-- Prove2me | Theorems.Thm_DelaunayStretch_lemma_3_3_exact_update
-- name    : DelaunayStretch.lemma_3_3_exact_update
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:53:52.202517+00:00
-- url     : https://prove2.me/theorems/2497a8a4-571c-4039-b93b-a5da2408a042
-- title:
--   Lemma 3.3 — exact update of $\delta_i$ and $\mu_i$ gate by gate
-- statement:
--   Fix a disk chain $(O_1,\dots,O_n;u,v)$ with $n\ge2$. For $1\le i\le n$ let $\alpha_i$ and $\beta_i$ be the lengths of the upper and lower rails of $O_i$. Then, for $0\le i\le n-1$,
--
--   $$
--   \delta_{i+1}=\mathrm{clip}_{|G_{i+1}|}(\delta_i+\alpha_{i+1}-\beta_{i+1}),\qquad \mu_{i+1}=\mu_i+\tfrac12(\alpha_{i+1}+\beta_{i+1}-\omega_{i+1}),
--   $$
--
--   where $\omega_{i+1}=(|\delta_i+\alpha_{i+1}-\beta_{i+1}|-|G_{i+1}|)_+$. In particular, since $|G_n|=0$,
--
--   $$
--   P(u,v)=\mu_n=\mu_{n-1}+\min\big(\tfrac12\delta_{n-1}+\alpha_n,\ -\tfrac12\delta_{n-1}+\beta_n\big).
--   $$
--
--   The lemma makes the cost of each disk a local quantity, the basis of the accounting identity (3.6).
--
--   **Formalization Note** $\mu_i$, $\delta_i$ are defined from shortest-path lengths in the prefix graphs, not by this recursion; $t_+=\max(t,0)$.
--
--   Differences from the source:
--   - encoding: shortest-path lengths d±ᵢ in the i-th prefix graph → infima of walk weights in the i-th prefix graph; reason: the graph is finite with nonnegative weights, so the infimum is attained and equals the shortest-path length
--   - encoding: points of ℝ² with coordinates x(z), y(z) and Euclidean norm → points of ℂ with x = re, y = im and ‖z − w‖ = dist z w; reason: ℂ is ℝ² with the Euclidean norm; same instances
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Lemma 3.3, pp.15–16 (standing assumption n ≥ 2, p.15)

import Mathlib
import Definitions.Def_DelaunayStretch_ChainInequality

namespace DelaunayStretch

/-- **Lemma 3.3 (Exact update)** (pp.15–16). Fix a disk chain `(O₁, …, Oₙ; u, v)` with
`n ≥ 2`. For `1 ≤ i ≤ n`, let `αᵢ` and `βᵢ` be the lengths of the upper and lower rails of
`Oᵢ`. Then, for `0 ≤ i ≤ n − 1`,
`δᵢ₊₁ = clip_{|Gᵢ₊₁|}(δᵢ + αᵢ₊₁ − βᵢ₊₁)`, `µᵢ₊₁ = µᵢ + ½(αᵢ₊₁ + βᵢ₊₁ − ωᵢ₊₁)` (3.2),
where `ωᵢ₊₁ = (|δᵢ + αᵢ₊₁ − βᵢ₊₁| − |Gᵢ₊₁|)₊`. In particular, for `i = n − 1`, since `|Gₙ| = 0`,
`P(u, v) = µₙ = µₙ₋₁ + min(½δₙ₋₁ + αₙ, −½δₙ₋₁ + βₙ)` (3.3).

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Lemma 3.3, pp.15–16 (standing assumption `n ≥ 2`, p.15).

**Formalization Note** `µᵢ`, `δᵢ` are defined from shortest-path lengths in the prefix graphs
(`DiskChain.mu`, `DiskChain.delta`, Definition 3.1), not by this recursion. `t₊ = max(t, 0)`. -/
theorem lemma_3_3_exact_update (C : DiskChain) (hC : C.IsDiskChain) (hn : 2 ≤ C.n) :
    (∀ i, i + 1 ≤ C.n →
      C.delta (i + 1) =
          clip (C.gateLength (i + 1)) (C.delta i + C.upperRail (i + 1) - C.lowerRail (i + 1)) ∧
        C.mu (i + 1) = C.mu i + (C.upperRail (i + 1) + C.lowerRail (i + 1) -
          max (|C.delta i + C.upperRail (i + 1) - C.lowerRail (i + 1)| - C.gateLength (i + 1)) 0)
            / 2) ∧
    C.shortestPath = C.mu C.n ∧
    C.mu C.n = C.mu (C.n - 1) +
      min (C.delta (C.n - 1) / 2 + C.upperRail C.n) (-C.delta (C.n - 1) / 2 + C.lowerRail C.n) := by sorry

end DelaunayStretch
