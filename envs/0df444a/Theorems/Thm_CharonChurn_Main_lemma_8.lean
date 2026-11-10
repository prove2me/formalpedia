-- Prove2me | Theorems.Thm_CharonChurn_Main_lemma_8
-- name    : CharonChurn.Main.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:56:41.849013+00:00
-- url     : https://prove2.me/theorems/6024fe07-bc50-4266-bc29-42edc708e940
-- title:
--   Lemma 8 — connectivity after deleting Byzantine vertices
-- statement:
--   In every round $r$, the graph induced by the correct processes $C_r=V_r\setminus B$ satisfies $\kappa(G_r[C_r])\ge\rho=t+2c+1$.
--
--   Differences from the source:
--   - generalization: for every round r, under the standing assumptions of the model → for a fixed round r, assuming only that round's assumptions (n vertices, B ⊆ V_r, D-regular, gap, κ(G_r) > 2(t+c)) and |B| ≤ t; reason: the proof uses only round r; an admissible network satisfies these hypotheses in every round, so the source statement follows
-- source:
--   Sengupta and Perrin (2026), Byzantine Partition Detection Under Churn, supplied 48-page artifact (venue metadata: STOC 2027 submission; citation basis published per source.meta.json; SHA-256 3f9994406f38c73927d0b5cc78d0dd05740de0f7d09e544b7b203eefe39cdb74), Lemma 8, p. 20 (PDF 20)

import Mathlib
import Definitions.Def_CharonChurn_Main_Network

namespace CharonChurn.Main

/-- Lemma 8 (Connectivity after deleting Byzantine vertices), p. 20. In every round `r`,
`κ(G_r[C_r]) ≥ ρ = t + 2c + 1`. -/
theorem lemma_8 (P : Params) (N : Network) (r : ℕ) (hround : RoundOK P N r)
    (hB : N.B.card ≤ P.t) :
    P.t + 2 * P.c + 1 ≤ kappa (N.G r) (correctSet N r) := by sorry

end CharonChurn.Main
