-- Prove2me | Theorems.Thm_ForgetAlt_lemma_3_13
-- name    : ForgetAlt.lemma_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:24:41.701414+00:00
-- url     : https://prove2.me/theorems/75c61676-e317-4a3a-8d11-dd8b02fa43cb
-- title:
--   Lemma 3.13: edges between different postdominator classes have volume $\ge 2\ell+5$
-- statement:
--   Every edge $e=\{y,z\}$ of $G$ with $y,z\in V(H_0)$ and $\mathrm{cl}(y)\ne\mathrm{cl}(z)$ satisfies
--
--   $$\mathrm{vlevel}(e)\ge 2\ell+5.$$
--
--   Differences from the source:
--   - encoding: graphs are finite (standing convention of the paper) → a finite vertex type, [Finite V]; reason: Lean convention; every graph of the paper is finite
--   - encoding: ℓ, with 2ℓ + 1 the length of a shortest augmenting path (|U| ≥ 2 assumed throughout) → hypothesis HasAugPath M; reason: ℓ is undefined when (G, M) has no augmenting path; the hypothesis only excludes that case
--   - encoding: y, z ∈ V(H₀) → y and z reachable from f; reason: V(H₀) is the reachable original vertices
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Lemma 3.13, printed p.24 (PDF p.25)

import Mathlib
import Definitions.Def_ForgetAlt_DoublePathABD

namespace ForgetAlt

open BergeMatching.Core

/-- **Lemma 3.13**, printed p.24 (PDF p.25). Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…).

"Every edge `e = {y, z}` of `G` with `y, z ∈ V(H₀)` and `cl(y) ≠ cl(z)` satisfies
`vlevel(e) ≥ 2ℓ + 5`."

**Formalization Note.** `V(H₀)` = original vertices reachable from `f`; `cl = cl_{H₀}`. -/
theorem lemma_3_13 {V : Type} [Finite V] (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching)
    (hA : HasAugPath M) (y z : V) (hyz : G.Adj y z) (hy : Reach G M (.orig y))
    (hz : Reach G M (.orig z)) (hcl : cl (h0Adj G M) y ≠ cl (h0Adj G M) z) :
    ((2 * ell M + 5 : ℕ) : ℕ∞) ≤ vlevelE G M s(.orig y, .orig z) := by sorry

end ForgetAlt
