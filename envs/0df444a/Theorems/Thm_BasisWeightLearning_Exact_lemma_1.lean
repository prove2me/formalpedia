-- Prove2me | Theorems.Thm_BasisWeightLearning_Exact_lemma_1
-- name    : BasisWeightLearning.Exact.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:21:13.390635+00:00
-- url     : https://prove2.me/theorems/74dca634-af3a-412f-8ae4-31c3badba4a5
-- title:
--   Lemma 1 — Basis evaluation respects addition and convolution
-- statement:
--   Let $a,b$ be arbitrary signed finite polynomial weight vectors, possibly of different lengths, and let $\Phi$ contain enough monomials. Then both identities hold:
--   $$\Phi a+\Phi b=\Phi(a+b),\qquad (\Phi a)\odot(\Phi b)=\Phi(a\otimes b).$$
--   Here $\odot$ is pointwise multiplication and $\otimes$ is ordinary coefficient convolution. Equality holds as functions on all of $[0,1]$. This relates coefficient arithmetic to the represented continuation functions.
--
--   Differences from the source:
--   - reading: Definition 4 says max(d_a,d_b) components → zero padding through index max(d_a,d_b), hence max(d_a,d_b)+1 components; reason: the zero-based indices and the preceding 3- and 4-dimensional example determine this intended reading; see insight I1
--   - encoding: finite signed weight vectors of variable length, with padding and convolution → canonical real polynomials, with polynomial addition and multiplication and finite coordinate projections; reason: finite coefficient sequences modulo trailing zeros give exactly the same weights, evaluations and finite-dimensional strict exposure tests
--   - encoding: functions on [0,1] and Lebesgue integration → functions on the interval subtype with the pullback of real Lebesgue measure; reason: equality is exactly equality on the source domain and every admissible L2 density remains available
-- source:
--   Hao Zhang, Dynamic Learning and Decision Making via Basis Weight Vectors, Operations Research (2022), DOI 10.1287/opre.2021.2240, supplied PDF p. 15 (printed p. 15), Lemma 1; proof PDF p. 52 (EC p. 8).

import Definitions.Def_BasisWeightLearning_Exact_PolynomialWeights

namespace BasisWeightLearning.Exact
theorem lemma_1 (a b : Weight) :
    evaluate a + evaluate b = evaluate (a + b) ∧
    evaluate a * evaluate b = evaluate (a * b) := by sorry
end BasisWeightLearning.Exact
