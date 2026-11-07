-- Prove2me | Theorems.Thm_DetCCHard_lemma_6_3
-- name    : DetCCHard.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:58.765342+00:00
-- url     : https://prove2.me/theorems/72e793fd-97f3-47b8-b62c-8d5ed35d7dbb
-- title:
--   Lemma 6.3 — YES graphs admit collision-free bin assignments; NO graphs force $\zeta q_2$ collisions after small deletions
-- statement:
--   Let $s \ge 4$ be a power of two, let $G = (V, E)$ be a nonempty loopless multigraph with no isolated vertices and maximum degree at most $\Delta \ge 1$, let $n = |V|$, and let $q_2 = q_0 2^t$ be a dyadic multiple of $q_0 = \mathrm{pow2}(4s|E|)$. Consider the items $I = [4s] \times (V \sqcup [s-3])$ and their activity at the indices $\alpha \in [q_2]$ (Definition 6.2).
--
--   1. If $G$ is 3-colorable, there is an assignment of $I$ to the $s$ bins with at most one active item in each bin at every coordinate.
--   2. If every 3-coloring of $G$ has at least $\gamma|E|$ monochromatic edge occurrences ($\gamma > 0$), delete fewer than $(s/2)\,\delta_v n$ vertex items and fewer than $s/2$ auxiliary items, where
--   $$
--   \delta_v = \frac{\gamma |E|}{2\Delta n}, \qquad \zeta = \frac{\gamma}{24}.
--   $$
--   Then every assignment of the remaining items to the $s$ bins has at least $\zeta q_2$ coordinates at which one bin contains two active items and an inactive item.
--
--   The collisions of the NO case are what force the extra bit of the NO cost.
--
--   **Formalization Note** Deletions are counted in items, strictly. An assignment is a function on all items, of which only the values on remaining items matter. $\zeta q_2$ is compared in $\mathbb R$.
--
--   Differences from the source:
--   - generalization: the fixed constants Δ, γ of Theorem 5.2 and a graph produced by that reduction → every Δ ≥ 1, γ > 0 and every graph with the shape of Theorem 5.2 satisfying the promise; reason: the proof uses only these properties; the paper's graphs and constants are a special case
--   - encoding: the base coordinates in "a fixed order" on I → base coordinate β < 4s|E| is edge occurrence β mod |E| of group ⌊β/|E|⌋, copies of a base coordinate consecutive; reason: the paper leaves the order open; the number of collision coordinates does not depend on it
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Lemma 6.3, p.21 (items and coordinates: Definition 6.2, p.19)

import Mathlib
import Definitions.Def_DetCCHard_SrcGraph
import Definitions.Def_DetCCHard_pow2
import Definitions.Def_DetCCHard_Item

namespace DetCCHard

open Classical in
/-- **Lemma 6.3 (collisions)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256
ad552d13…a4a03, Lemma 6.3, p.21; items and coordinates from Definition 6.2, p.19). Let `s ≥ 4` be
a power of two and `q₂ = q₀·2^t` a dyadic multiple of `q₀ = pow2(4s|E|)`, and let `G` be a source
graph (nonempty, loopless, no isolated vertices, maximum degree at most `Δ`). A YES graph admits an
assignment of the items `I` to the `s` bins with at most one active item in each bin at every
coordinate. For a NO graph with gap `γ`, delete fewer than `(s/2)δ_v n` vertex items and fewer
than `s/2` auxiliary items, where `δ_v = γ|E|/(2Δn)` and `ζ = γ/24`; every assignment of the
remaining items to the `s` bins has at least `ζ q₂` coordinates at which one bin contains two
active items and an inactive item.

**Formalization Note** The constants `Δ ≥ 1` and `γ > 0` are arbitrary (in the paper they are the
fixed constants of Theorem 5.2, which is a special case). Deletions are counted in items (vertex
items `(g, inl v)`, auxiliary items `(g, inr a)`), strictly. An assignment is a function on all
items, of which only its values on the remaining items matter. `ζ q₂` is compared in `ℝ`. -/
theorem lemma_6_3 (Δ : ℕ) (hΔ : 1 ≤ Δ) (γ : ℚ) (hγ : 0 < γ) (G : SrcGraph) (hG : IsShape Δ G)
    (s : ℕ) (hs4 : 4 ≤ s) (hs : ∃ e : ℕ, s = 2 ^ e) (t q₂ : ℕ)
    (hq₂ : q₂ = baseCoordCount G s * 2 ^ t) :
    (IsYes G → ∃ χ : Item s G.n → Fin s, ∀ α < q₂, ∀ i₁ i₂ : Item s G.n,
        active G s t i₁ α → active G s t i₂ α → χ i₁ = χ i₂ → i₁ = i₂) ∧
    (IsNo γ G → ∀ Del : Finset (Item s G.n),
        (((Del.filter fun i => i.2.isLeft).card : ℝ) <
          (s / 2 : ℝ) * ((γ : ℝ) * G.edges.length / (2 * Δ * G.n)) * G.n) →
        (((Del.filter fun i => i.2.isRight).card : ℝ) < (s / 2 : ℝ)) →
        ∀ χ : Item s G.n → Fin s,
          ((γ : ℝ) / 24) * q₂ ≤
            (((Finset.range q₂).filter fun α =>
              IsCollision G s t (↑(Finset.univ \ Del)) χ α).card : ℝ)) := by sorry

end DetCCHard
