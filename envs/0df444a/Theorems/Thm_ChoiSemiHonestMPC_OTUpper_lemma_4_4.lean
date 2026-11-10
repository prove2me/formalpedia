-- Prove2me | Theorems.Thm_ChoiSemiHonestMPC_OTUpper_lemma_4_4
-- name    : ChoiSemiHonestMPC.OTUpper.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:28:18.9772+00:00
-- url     : https://prove2.me/theorems/6af0bd59-bdc1-4d73-8e4c-75cc11072ce3
-- title:
--   Lemma 4.4 — sequential exposure within one subset
-- statement:
--   Let $E$ be a uniform $t$-subset of $\{0,\dots,m-1\}$, let $C_1,\dots,C_K$ be pairwise disjoint candidate sets, and fix $i$ and subsets $e_j$ ($j<i$) such that the event $\{E\cap C_j=e_j\ \forall j<i\}$ has positive probability. Conditional on this event, $E\setminus\bigcup_{j<i}C_j$ is a uniform subset of size $t_i=t-\sum_{j<i}|e_j|$ of the remaining pool, which has $m_i=m-\sum_{j<i}|C_j|$ positions.
--
--   Differences from the source:
--   - encoding: server labels [n] = {1,…,n}; positions and tags counted from 1 → `Fin n` = {0,…,n−1}; positions and tags counted from 0; reason: relabelling by −1 changes no instance
--   - encoding: candidate sets determined by data independent of E; conditional on the candidate sets → fixed candidate sets; reason: conditioning on data independent of E leaves E uniform, so the statement for each fixed value of the data is the source statement
--   - encoding: conditional on the revealed subsets E_j = E ∩ C_j (j < i) → conditional on the event E ∩ C_j = e_j for j < i, assumed of positive probability; reason: conditioning on a null event is undefined
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Lemma 4.4, p. 17 (PDF 19)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Prob

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- Lemma 4.4 (sequential exposure within one subset). -/
theorem lemma_4_4 (m t K : ℕ) (htm : t ≤ m) (C : Fin K → Finset (Fin m))
    (hdisj : Pairwise fun j k => Disjoint (C j) (C k)) (i : Fin K)
    (e : Fin K → Finset (Fin m))
    (hfeas : 0 < probE (unifSubsets Finset.univ t) fun E => ∀ j, j < i → E ∩ C j = e j) :
    (pcond (unifSubsets Finset.univ t) fun E => ∀ j, j < i → E ∩ C j = e j).map
        (fun E => E \ (Finset.univ.filter fun j => j < i).biUnion C) =
      unifSubsets (Finset.univ \ (Finset.univ.filter fun j => j < i).biUnion C)
        (t - ∑ j ∈ Finset.univ.filter (fun j => j < i), (e j).card) ∧
    (Finset.univ \ (Finset.univ.filter fun j => j < i).biUnion C).card =
      m - ∑ j ∈ Finset.univ.filter (fun j => j < i), (C j).card := by sorry

end ChoiSemiHonestMPC.OTUpper
