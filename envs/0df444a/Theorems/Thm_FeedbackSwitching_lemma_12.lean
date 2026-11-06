-- Prove2me | Theorems.Thm_FeedbackSwitching_lemma_12
-- name    : FeedbackSwitching.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:39:09.062304+00:00
-- url     : https://prove2.me/theorems/09082aea-7dbc-4f99-99d9-1105de35a3d5
-- title:
--   Lemma 12 — a set of $\ge\gamma/(16\log K)$ pairwise non-adjacent actions, each action observing $\le1+\log K$ of them
-- statement:
--   Let $G$ be an observable graph on $K\ge2$ actions with domination number $\gamma(G)\ge32\log K$. There is a set $S$ of at least $\gamma(G)/(16\log K)$ actions with no edges between distinct members such that every action observes at most $1+\log K$ members of $S$.
--
--   Such a set satisfies the hypothesis of Proposition 4 with $m=1+\log K$, which turns a large domination number into a lower bound.
--
--   **Formalization Note** Members may have self-loops; "observes" counts self-loops.
--
--   Differences from the source: none.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Lemma 12, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_FeedbackSwitching_FeedbackGraph
open scoped Classical

namespace FeedbackSwitching

/-- **Lemma 12 (Sets with few observers)**, p.37 (PDF p.39). Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, *The Price of Partial Information with
Switching Costs: A Complete Characterization for Feedback Graphs*, arXiv:2606.03851 (held version,
sha256 ded8f8bc…).

"Let `G` be an observable graph on `K ≥ 2` actions with domination number `γ(G) ≥ 32 log K`. There
is a set of at least `γ(G)/(16 log K)` actions, with no edges between distinct members, such that
every action observes at most `1 + log K` of them."

**Formalization Note.** "No edges between distinct members": `¬ G u v` for distinct `u, v ∈ S`
(self-loops of members are allowed). "Observes" counts self-loops. Sizes are compared in `ℝ`. -/
theorem lemma_12 {K : ℕ} (hK : 2 ≤ K) (G : FeedbackGraph K) (hG : Observable G)
    (hγ : 32 * Real.log K ≤ (dominationNumber G : ℝ)) :
    ∃ S : Finset (Fin K),
      (dominationNumber G : ℝ) / (16 * Real.log K) ≤ S.card ∧
      (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G u v) ∧
      ∀ a, ((S.filter (fun v => G a v)).card : ℝ) ≤ 1 + Real.log K := by sorry

end FeedbackSwitching
