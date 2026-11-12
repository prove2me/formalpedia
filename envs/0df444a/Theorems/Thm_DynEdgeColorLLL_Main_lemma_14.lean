-- Prove2me | Theorems.Thm_DynEdgeColorLLL_Main_lemma_14
-- name    : DynEdgeColorLLL.Main.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:13.573755+00:00
-- url     : https://prove2.me/theorems/3396fd40-618a-4e7b-b8f3-46c2c1a0ceaf
-- title:
--   Lemma 14 — Search keeps the seed-failure set complete
-- statement:
--   Work in the regime of §5.1–§6. Let one update insert or delete the edge $e=\{u,v\}$, turning $G^{old}$ into $G^{new}$, both of maximum degree at most $\Delta$. Fix any directions and categories in $[m_d]$, shared by both instances. Let $F^{new}$ be the result of the failure discovery stage started from $F^{old}$. Then
--   $$F^{old}\text{ complete for the old instance}\ \Longrightarrow\ F^{new}\text{ complete for the new instance}.$$
--
--   The statement is deterministic. Since $\bar{\rm A}$ needs a complete $F$, this lemma lets the dynamic algorithm maintain the input of $\bar{\rm A}$ across updates.
--
--   **Formalization Note.** The Search calls visit each pair at most once. The visited pairs are therefore the least set that contains the initial calls and is closed under the recursive calls made from visited pairs that are seed failures after the update. This set does not depend on the order of the calls.
--
--   Differences from the source:
--   - encoding: the recursive Search procedure with a visited bit per pair → the visited set as an inductive predicate (least closed set) and F^new defined from it; reason: with every pair visited once, the outcome is order-independent and equals this set
--   - reading: "Δ_ε large enough" and Δ > exp(Δ_ε) → an absolute D₀ with the statement for every real E ≥ D₀ and every Δ > exp(E); reason: the existential threshold is the meaning of "large enough"
--   - reading: log in q_d → log base 2; reason: same strength for either base
--   - encoding: random choices fixed for the lifetime of an edge → every realization, shared by both instances, with categories in [m_d] for the edges of both graphs; reason: the statement is deterministic
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Lemma 14, printed p. 28 (PDF p. 30); Failure Discovery Stage, printed p. 28 (PDF p. 30)

import Mathlib
import Definitions.Def_DynEdgeColorLLL_Main_Splitting
import Definitions.Def_DynEdgeColorLLL_Main_DynamicSplitting

namespace DynEdgeColorLLL.Main

open Classical in
/-- Lemma 14 (Peng–Ghaffari, STOC 2027 submission #615, printed p. 28, PDF p. 30). In the regime of
§5.1–§6, for every single-edge update `G^old → G^new` of graphs of maximum degree at most `Δ` and
every realization of the random choices (shared by both instances): if `F^old` is complete for the
old instance, then the set `F^new` produced by the Search calls of the failure discovery stage is
complete for the new instance. -/
theorem lemma_14 :
    ∃ D₀ : ℝ, ∀ E : ℝ, D₀ ≤ E → ∀ Δ : ℕ, Real.exp E < Δ →
      ∀ {V : Type} [Fintype V] [DecidableEq V]
      (Gold Gnew : SimpleGraph V) (u v : V) (c : Choices V) (Fold : Set (V × List Bool)),
      IsEdgeUpdate Gold Gnew u v → (∀ x, Gold.degree x ≤ Δ) → (∀ x, Gnew.degree x ≤ Δ) →
      ValidCategories Δ E Gold c → ValidCategories Δ E Gnew c →
      IsComplete Δ E Gold c Fold →
      IsComplete Δ E Gnew c (searchResult Δ E Gold Gnew c u v Fold) := by sorry

end DynEdgeColorLLL.Main
