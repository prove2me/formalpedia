-- Prove2me | Theorems.Thm_DetConnSketch_Main_lemma_4_3
-- name    : DetConnSketch.Main.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:42:09.012076+00:00
-- url     : https://prove2.me/theorems/904222eb-d923-4829-a8bf-6d3522f67b59
-- title:
--   Lemma 4.3 — $m+1$ subgraphs with $\le 2m/3$ edges, one of which halves every cut of each $G\subseteq F$ within $4\sqrt{nm}$
-- statement:
--   Let $F$ be a graph on $n$ labeled vertices with $m = |E(F)| \ge n^{7/4}$ edges. Then there are $m+1$ subgraphs $M_1, \dots, M_{m+1}$ of $F$, each with at most $2m/3$ edges, such that every subgraph $G \subseteq F$ has an index $i \in [m+1]$ with
--   $$\big|\delta_G(S) - 2\,\delta_{G \cap M_i}(S)\big| \le 4\sqrt{nm} \qquad \text{for every cut } S \subseteq V,$$
--   where $\delta$ is the cut size. The subgraphs depend on $F$ only; the index depends on $G$.
--
--   This is the recursion step of the $\tilde O(n^{7/4})$ protocol (Theorem 4.1): storing the index $i$ lets the protocol pass to the smaller parent graph $M_i$ while keeping every cut of $G$ within $O(\sqrt{nm})$ of twice the corresponding cut of $G\cap M_i$.
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1, …, n} → Fin n (0-based); reason: Lean indexing; same objects
--   - reading: a fixed set of subgraphs M_1, …, M_{m+1} → each M i ≤ F (subgraphs of the parent graph F), indexed by Fin (m + 1); reason: the proof samples the edges of F; since G ⊆ F, G ∩ M_i depends only on M_i ∩ F, so the reading changes no instance
--   - encoding: each with ≤ 2m/3 many edges → 3 · |E(M i)| ≤ 2 · |E(F)| in ℕ (edge counts as Set.ncard); reason: same inequality without division
--   - encoding: cut S ⊆ V and δ_G(S) → S : Finset (Fin n) and cutSize G S; reason: same quantity
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 21 (PDF 25), Lemma 4.3

import Mathlib
import Definitions.Def_DetConnSketch_Main_CutSize

namespace DetConnSketch.Main

/-- Lemma 4.3: for a parent graph `F` on `Fin n` with `m = |E(F)| ≥ n^{7/4}` edges there are
`m + 1` subgraphs `M_1, …, M_{m+1}` of `F`, each with at most `2m/3` edges, such that every
subgraph `G ⊆ F` has an index `i` with `|δ_G(S) − 2 δ_{G ∩ M_i}(S)| ≤ 4√(nm)` for every cut `S`. -/
theorem lemma_4_3 (n : ℕ) (F : SimpleGraph (Fin n))
    (hF : (n : ℝ) ^ ((7 : ℝ) / 4) ≤ (F.edgeSet.ncard : ℝ)) :
    ∃ M : Fin (F.edgeSet.ncard + 1) → SimpleGraph (Fin n),
      (∀ i, M i ≤ F ∧ 3 * (M i).edgeSet.ncard ≤ 2 * F.edgeSet.ncard) ∧
      ∀ G : SimpleGraph (Fin n), G ≤ F → ∃ i, ∀ S : Finset (Fin n),
        |(cutSize G S : ℝ) - 2 * (cutSize (G ⊓ M i) S : ℝ)| ≤
          4 * Real.sqrt ((n : ℝ) * (F.edgeSet.ncard : ℝ)) := by sorry

end DetConnSketch.Main
