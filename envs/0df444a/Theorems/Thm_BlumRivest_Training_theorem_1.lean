-- Prove2me | Theorems.Thm_BlumRivest_Training_theorem_1
-- name    : BlumRivest.Training.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:43:30.20502+00:00
-- url     : https://prove2.me/theorems/9d914b2c-4707-4b9b-bf9e-cb4df8cfd169
-- title:
--   Theorem 1 — Training the 3-Node Network is NP-complete
-- statement:
--   Consider the network with two hidden linear threshold nodes, each receiving all $n$ Boolean inputs, and one trainable linear threshold output node receiving the numerical −1/+1 hidden outputs. All weights and thresholds at all three nodes are arbitrary real numbers. Each node outputs +1 exactly when its weighted input sum is strictly greater than its threshold, and −1 otherwise.
--
--   Let $L_{\mathrm{training}}$ contain the explicit codes of all finite labeled training instances, over all dimensions $n\in\mathbb N$, for which some choice of these real parameters agrees with every label. Then
--
--   $$\operatorname{NPComplete}(L_{\mathrm{training}}).$$
--
--   This asserts both membership in NP and polynomial-time many-one hardness for every NP language over every finite nonempty alphabet. There is no bound on the number of examples, no realizability promise, and no restriction of the output node to AND. Neither a source problem's hardness nor the existence of finite certificates is assumed. Empty data and dimension zero are included; malformed strings are outside the language.
--
--   Differences from the source:
--   - encoding: points in {0,1}^n with signs + and − → Fin n coordinates, Boolean labels with true positive, and finite lists; reason: every finite source data set can be listed, and order and repeated identical pairs do not affect exact agreement.
--   - encoding: a decision problem on explicit Boolean examples → a five-symbol language with a unary dimension header, explicit rows, and malformed strings rejected; reason: the code has length n+1+m(n+2) and preserves the explicit vector input.
-- source:
--   Blum and Rivest (1992), Theorem 1, printed p. 119 (PDF p. 3), with Definition 1 on printed pp. 118–119 (PDF pp. 2–3), DOI 10.1016/S0893-6080(05)80010-3.

import Definitions.Def_BlumRivest_Training_Encoding

namespace BlumRivest.Training

theorem theorem_1 :
    CookPvsNP.NPComplete trainingLanguage := by sorry

end BlumRivest.Training
