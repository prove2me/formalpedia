-- Prove2me | Theorems.Thm_EssCheck_Accuracy_lemma_3
-- name    : EssCheck.Accuracy.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:16.597015+00:00
-- url     : https://prove2.me/theorems/e0f8ccb5-78d2-4d46-ab77-59c1c2c2b5fe
-- title:
--   Lemma 3 — private research incentive exceeds the social incentive
-- statement:
--   When the maximum royalty fraction is $\bar\alpha=1$, fix any partition of the value states into hybrid states $H$ and pooling states $P$, and any accuracy $\beta\in[0,1]$. The private incentive to invest in research exceeds the social incentive in the sense that the left-hand side of equation (5) is at least the left-hand side of equation (7):
--   $$\operatorname{socialWedge}(H)\le\operatorname{privateWedge}(H,\beta).$$
--   This is the wedge comparison used to sign the welfare derivative in Proposition 1.
--
--   **Formalization Note** The result quantifies over a partition of all finite value states, reflecting the paper's instruction to fix $H$ and $P$ during this comparison.
-- source:
--   Schuett & Wipusanawan, Essentiality Checks for Standard Essential Patents, TILEC Discussion Paper DP 2023-21 (Dec. 2023; SSRN 4688864), p. 23 (PDF 24), Lemma 3 and first sentence of its proof

import Mathlib
import Definitions.Def_EssCheck_Accuracy_Model

namespace EssCheck.Accuracy

theorem lemma_3 {n : ℕ} (M : Model n) (hS : M.Standing)
    (hα : M.αbar = 1) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (S : Finset (Fin n)) :
    socialWedge M S ≤ privateWedge M S β := by sorry

end EssCheck.Accuracy
