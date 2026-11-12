-- Prove2me | Theorems.Thm_DecrNearAddAPSP_W2_lemma_2_4
-- name    : DecrNearAddAPSP.W2.lemma_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:13:23.082197+00:00
-- url     : https://prove2.me/theorems/4f889a0f-3ad3-4325-bc61-78ff7e9f102f
-- title:
--   Lemma 2.4 [HKN15] — monotone ES-tree levels: exact at time 0, never below δ_H, never decreasing, supported when they increase
-- statement:
--   Let $H_0,H_1,\dots$ be a sequence of weighted graphs on $V=\{0,\dots,n-1\}$ with positive integer weights (any edge may be deleted, inserted, made heavier or lighter between consecutive times), let $s$ be a root and $\tau$ a depth, and let $\ell_t$ be the levels of the monotone ES-tree of $H$ rooted at $s$ maintained up to distance $\tau$ (the least admissible level functions; see the definition). Then:
--
--   1. initially $\ell_0(v)=\delta_{H_0}(s,v)$ for every $v$ with $\delta_{H_0}(s,v)\le\tau$;
--   2. $\delta_{H_t}(s,v)\le\ell_t(v)$ at all times $t$;
--   3. $\ell_t(v)$ never decreases: $\ell_t(v)\le\ell_{t+1}(v)$;
--   4. whenever $\ell_t(v)<\ell_{t+1}(v)\le\tau$,
--   $$
--   \ell_{t+1}(v)=\min_{x\in N_{t+1}(v)}\big\{\ell_{t+1}(x)+w_{H_{t+1}}(x,v)\big\},
--   $$
--   where $N_{t+1}(v)$ is the neighbourhood of $v$ in $H_{t+1}$.
--
--   These are the invariants through which every stretch argument of the paper uses Monotone ES-trees: levels are valid lower bounds that can lag behind distances only through stretched edges.
--
--   Differences from the source:
--
--   - encoding: a monotone ES-tree of H rooted at s, maintained up to distance τ (operational description, pp. 7–8) → monoLevels: ℓ_0 the least admissible level function of H_0, ℓ_{t+1} the least admissible one of H_{t+1} above ℓ_t; levels in {0, …, τ} ∪ {∞}; reason: the page's rules (no relaxation on insertion, a level rises only when every incoming edge fails, the min-invariant, levels above τ disconnected) describe exactly this least fixed point
--   - reading: H a graph undergoing edge deletions, insertions, weight increases and decreases, weights as in §2 → an arbitrary sequence H : ℕ → WGraph (Fin n) with every weight ≥ 1; reason: every sequence of graphs is produced by such updates; positive weights are §5's standing assumption, and with a 0-weight edge two unsupported endpoints at equal level satisfy the invariant, so clause (2) needs them
--   - reading: (4) whenever ℓ_s(v) increases to a value ≤ τ, ℓ_s(v) = min_{x∈N(v)}{ℓ_s(x) + w_H(x, v)} → for every t: ℓ_t(v) < ℓ_{t+1}(v) ≤ τ implies ℓ_{t+1}(v) = ⨅_{x ∈ N_{H_{t+1}}(v)} (ℓ_{t+1}(x) + w_{t+1}(x, v)); reason: an increase happens between consecutive times; N(v) and w_H are those of the current graph
--   - encoding: vertex set V, distances δ_H → V = Fin n; δ_H in ℕ∞; reason: Lean convention; same instances
-- source:
--   Koveshi, Roditty, Sapir, First Near-Additive All-Pairs Approximate Shortest Paths in Decremental Weighted Graphs, arXiv:2611.04635 (PDF sha256 6bb2b230…), p. 8, Lemma 2.4

import Mathlib
import Definitions.Def_DecrNearAddAPSP_W2_Graphs
import Definitions.Def_DecrNearAddAPSP_W2_MonoES

namespace DecrNearAddAPSP.W2

/-- **Lemma 2.4** ([HKN15], p. 8). Let `H_0, H_1, …` be any sequence of weighted graphs on `Fin n`
with positive weights (edges may be deleted, inserted, made heavier or lighter), `s` a root and `τ`
a depth, and let `ℓ_t` be the levels of the monotone ES-tree of `H` rooted at `s` maintained up to
distance `τ`. Then (1) `ℓ_0(v) = δ_{H_0}(s, v)` for every `v` with `δ_{H_0}(s, v) ≤ τ`;
(2) `δ_{H_t}(s, v) ≤ ℓ_t(v)` for all `t, v`; (3) `ℓ_t(v) ≤ ℓ_{t+1}(v)`; (4) whenever
`ℓ_t(v) < ℓ_{t+1}(v) ≤ τ`, `ℓ_{t+1}(v) = min_{x ∈ N_{t+1}(v)} {ℓ_{t+1}(x) + w_{H_{t+1}}(x, v)}`. -/
theorem lemma_2_4 {n : ℕ} (H : ℕ → WGraph (Fin n)) (s : Fin n) (τ : ℕ)
    (hpos : ∀ t, (H t).PosWeights) :
    (∀ v, (H 0).dist s v ≤ (τ : ℕ∞) →
      monoLevels (fun t => (H t).toD) s τ 0 v = (H 0).dist s v) ∧
    (∀ t v, (H t).dist s v ≤ monoLevels (fun t => (H t).toD) s τ t v) ∧
    (∀ t v, monoLevels (fun t => (H t).toD) s τ t v ≤
      monoLevels (fun t => (H t).toD) s τ (t + 1) v) ∧
    (∀ t v, monoLevels (fun t => (H t).toD) s τ t v <
        monoLevels (fun t => (H t).toD) s τ (t + 1) v →
      monoLevels (fun t => (H t).toD) s τ (t + 1) v ≤ (τ : ℕ∞) →
      monoLevels (fun t => (H t).toD) s τ (t + 1) v =
        ⨅ x ∈ (H (t + 1)).adj.neighborSet v,
          (monoLevels (fun t => (H t).toD) s τ (t + 1) x + ((H (t + 1)).wt s(x, v) : ℕ∞))) := by sorry

end DecrNearAddAPSP.W2
