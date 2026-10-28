-- Prove2me | Theorems.Thm_CyberShare_Sharing_lemma_1
-- name    : CyberShare.Sharing.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:28.690169+00:00
-- url     : https://prove2.me/theorems/1211b2c4-8e25-4b9b-ac4a-29265457a04d
-- title:
--   Lemma 1 — unique price-stage equilibrium
-- statement:
--   Fix the paper's admissible parameters, realized attacks $\alpha_1,\alpha_2$, and nonnegative investments $K_1,K_2$. A pair of prices is an equilibrium of the constrained pricing stage if and only if, for each distinct $i,j\in\{1,2\}$,
--
--   $$
--   p_i^*=\frac{a+c}{2-b}+\alpha_i\frac{2(\delta-\gamma K_i)^+}{4-b^2}+\alpha_j\frac{b(\delta-\gamma K_j)^+}{4-b^2}.
--   $$
--
--   This identifies the unique price continuation used in the subsequent investment game.
--
--   **Formalization Note** Investments are nonnegative because they are chosen in the investment stage. The constrained price objective is the true profit in equation (4), with a price floor at the realized marginal cost. The proof text on p. A.3 drops $c$ from an intermediate best response; the displayed Lemma 1 formula includes it.
-- source:
--   August, Noh, Shamir & Shin, Cyberattacks, Operational Disruption and Investment in Resilience Measures, SSRN 4032257 (version of 2022-02-10), p. 10 (PDF 11), Lemma 1; proof p. A.3 (PDF 35); https://ssrn.com/abstract=4032257

import Mathlib
import Definitions.Def_CyberShare_Sharing_Model

namespace CyberShare.Sharing

/-- Lemma 1, p. 10 (PDF 11). Investments are nonnegative as required by the investment stage. -/
theorem lemma_1 (P : Params) (hP : P.Standing) (attack1 attack2 : Bool)
    (K1 K2 p1 p2 : ℝ) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) :
    IsPriceEq P attack1 attack2 K1 K2 p1 p2 ↔
      p1 = pStar P attack1 attack2 K1 K2 ∧
      p2 = pStar P attack2 attack1 K2 K1 := by sorry

end CyberShare.Sharing
