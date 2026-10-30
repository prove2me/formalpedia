-- Prove2me | Theorems.Thm_BasisWeightLearning_Exact_corollary_1
-- name    : BasisWeightLearning.Exact.corollary_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:22:23.207483+00:00
-- url     : https://prove2.me/theorems/34f2bee2-7e03-4376-b61a-cc758cf7d816
-- title:
--   Corollary 1 — Expected-reward coefficients
-- statement:
--   In the valid learning-and-doing model with finite nonempty action and signal sets, assume (A1): every probability and reward function has the supplied polynomial weight representation. For every action $a$,
--   $$\bar r(a)=\Phi w_{\bar r}(a),\qquad w_{\bar r}(a)=\sum_{s\in S}w_p(a,s)\otimes w_r(a,s).$$
--   The expected reward is $\bar r(a)(\theta)=\sum_s p(s\mid\theta,a)r(\theta,a,s)$. Signed coefficients and arbitrary finite degrees are allowed. The model retains probability normalization and $0<\delta\le1$.
--
--   Differences from the source:
--   - reading: Definition 4 says max(d_a,d_b) components → zero padding through index max(d_a,d_b), hence max(d_a,d_b)+1 components; reason: the zero-based indices and the preceding 3- and 4-dimensional example determine this intended reading; see insight I1
--   - encoding: finite signed weight vectors of variable length, with padding and convolution → canonical real polynomials, with polynomial addition and multiplication and finite coordinate projections; reason: finite coefficient sequences modulo trailing zeros give exactly the same weights, evaluations and finite-dimensional strict exposure tests
--   - encoding: functions on [0,1] and Lebesgue integration → functions on the interval subtype with the pullback of real Lebesgue measure; reason: equality is exactly equality on the source domain and every admissible L2 density remains available
-- source:
--   Hao Zhang, Dynamic Learning and Decision Making via Basis Weight Vectors, Operations Research (2022), DOI 10.1287/opre.2021.2240, supplied PDF p. 16 (printed p. 16), Corollary 1, Eq. (14).

import Definitions.Def_BasisWeightLearning_Exact_ExpectedReward
import Definitions.Def_BasisWeightLearning_Exact_PolynomialData

namespace BasisWeightLearning.Exact
theorem corollary_1 {A S : Type} [Fintype A] [Nonempty A] [Fintype S] [Nonempty S]
    (M : HiddenModel Theta A S) (hM : M.Valid)
    (D : PolynomialData A S) (hA1 : D.Represents M) (a : A) :
    expectedReward M a = evaluate (expectedWeight D a) := by sorry
end BasisWeightLearning.Exact
