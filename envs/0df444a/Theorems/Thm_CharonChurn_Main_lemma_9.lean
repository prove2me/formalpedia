-- Prove2me | Theorems.Thm_CharonChurn_Main_lemma_9
-- name    : CharonChurn.Main.lemma_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:56:52.971065+00:00
-- url     : https://prove2.me/theorems/641fb938-6235-4002-b436-bf0fe5b3febb
-- title:
--   Lemma 9 — boundary expansion on the correct vertices
-- statement:
--   Let $S\subseteq C_r$ with $|S|\le n/2$. Each of $A_S=\{u\in S: N_{G^C_r}(u)\cap(C_r\setminus S)\ne\emptyset\}$ and $B_S=\{v\in C_r\setminus S: N_{G^C_r}(v)\cap S\ne\emptyset\}$ has at least $\hat\lambda_0|S|/2-t$ elements (the bound may be nonpositive).
--
--   Differences from the source:
--   - generalization: round r of an execution satisfying the standing assumptions in every round → the parameter assumptions plus round r's assumptions and |B| ≤ t; reason: the proof uses only round r; specializes to every round of an admissible network
--   - encoding: |A_S|, |B_S| ≥ λ̂₀|S|/2 − t → real-valued inequalities on the cardinalities; reason: the bound is real and may be nonpositive; same content
-- source:
--   Sengupta and Perrin (2026), Byzantine Partition Detection Under Churn, supplied 48-page artifact (venue metadata: STOC 2027 submission; citation basis published per source.meta.json; SHA-256 3f9994406f38c73927d0b5cc78d0dd05740de0f7d09e544b7b203eefe39cdb74), Lemma 9, p. 20 (PDF 20)

import Mathlib
import Definitions.Def_CharonChurn_Main_Network

namespace CharonChurn.Main

open Classical in
/-- Lemma 9 (Boundary expansion on the correct vertices), p. 20. For `S ⊆ C_r` with
`|S| ≤ n/2`, both `A_S = {u ∈ S : N_{G^C_r}(u) ∩ (C_r \ S) ≠ ∅}` and
`B_S = {v ∈ C_r \ S : N_{G^C_r}(v) ∩ S ≠ ∅}` have at least `λ̂₀|S|/2 − t` elements. -/
theorem lemma_9 (P : Params) (N : Network) (r : ℕ) (hP : ParamsOK P) (hround : RoundOK P N r)
    (hB : N.B.card ≤ P.t) (S : Finset ℕ) (hS : S ⊆ correctSet N r)
    (hsize : (S.card : ℝ) ≤ (P.n : ℝ) / 2) :
    P.lam * S.card / 2 - P.t ≤
        ((S.filter (fun u => ∃ w ∈ correctSet N r \ S, (N.G r).Adj u w)).card : ℝ) ∧
      P.lam * S.card / 2 - P.t ≤
        (((correctSet N r \ S).filter (fun v => ∃ u ∈ S, (N.G r).Adj v u)).card : ℝ) := by sorry

end CharonChurn.Main
