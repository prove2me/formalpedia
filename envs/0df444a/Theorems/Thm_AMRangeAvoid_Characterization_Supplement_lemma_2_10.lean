-- Prove2me | Theorems.Thm_AMRangeAvoid_Characterization_Supplement_lemma_2_10
-- name    : AMRangeAvoid.Characterization.Supplement.lemma_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:26:57.599054+00:00
-- url     : https://prove2.me/theorems/abfdfda7-ddf6-445b-a372-b150029ea6c6
-- title:
--   Lemma 2.10 — Every finite group has logarithmically many generators
-- statement:
--   For every finite group $A$, including the trivial group, there exists a finite subset $\Gamma\subseteq A$ that generates $A$ and satisfies
--
--   $$\langle\Gamma\rangle=A,\qquad |\Gamma|\le\lceil\log_2|A|\rceil.$$
--
--   The result is uniform over all finite groups, rather than restricted to permutation groups. In the trivial group the empty set suffices. It supplies the generator-count bound used by the graph reduction.
--
--   Differences from the source:
--   - encoding: a finite group and the ceiling of its binary logarithmic order → a group with Fintype, subgroup closure, and Nat.clog 2 of its cardinality; reason: these express the same generating condition and integer bound, including order one
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), Lemma 2.10, printed p.11 (PDF p.13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_Supplement_Complexity
import Definitions.Def_AMRangeAvoid_Characterization_SSLB

namespace AMRangeAvoid.Characterization.Supplement

theorem lemma_2_10 (A : Type*) [Group A] [Fintype A] :
    ∃ Γ : Finset A, Subgroup.closure (Γ : Set A) = ⊤ ∧
      Γ.card ≤ Nat.clog 2 (Fintype.card A) := by sorry

end AMRangeAvoid.Characterization.Supplement
