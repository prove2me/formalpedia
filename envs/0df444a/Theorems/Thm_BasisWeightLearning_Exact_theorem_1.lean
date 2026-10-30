-- Prove2me | Theorems.Thm_BasisWeightLearning_Exact_theorem_1
-- name    : BasisWeightLearning.Exact.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:23:43.308935+00:00
-- url     : https://prove2.me/theorems/e865480e-bbc6-477e-a8ef-3b47d885215f
-- title:
--   Theorem 1 — Exact basis-weight backward recursion
-- statement:
--   Consider the fixed-hidden-parameter model on $\Theta=[0,1]$ with any finite horizon $T$, finite nonempty action and signal sets, nonnegative observation probabilities summing to one, real signal-dependent rewards and $0<\delta\le1$. Assume (A1), polynomial weight representations for all probability and reward functions, and (A2), polynomial weight representations for every member of the finite nonempty efficient terminal family $U_{T+1}^*$. Initialize
--   $$W_{T+1}^*=\{w(u):u\in U_{T+1}^*\}.$$
--   The independently defined function recursion is Eqs. (7)–(9), with the finite efficient terminal family permitted by (A2). It is solved by the weight recursion
--   $$W_t^*=\operatorname{PNEP}\left(\bigcup_{a\in A}W_t^*(a)\right),$$
--   $$W_t^*(a)=\operatorname{PNEP}\left(\left\{w_{\bar r}(a)+\delta\sum_{s\in S} w_p(a,s)\otimes w_{t+1}(s): w_{t+1}(s)\in W_{t+1}^*\ \forall s\right\}\right),$$
--   for every $t=1,\ldots,T$ and every action. The full function frontier is recovered exactly at every decision period:
--   $$U_t^*=\operatorname{PNEP}(\{\Phi w:w\in W_t^*\}).$$
--   The PNEP operations in coefficient and function space use their respective simplex and density normals. Polynomial degrees may grow arbitrarily through the recursion; coefficients may have either sign. The terminal function and weight identities, both weight recursions and the recovery set equality are conclusions of the statement. No induction invariant or frontier equivalence is assumed.
--
--   Differences from the source:
--   - reading: Definition 4 says max(d_a,d_b) components → zero padding through index max(d_a,d_b), hence max(d_a,d_b)+1 components; reason: the zero-based indices and the preceding 3- and 4-dimensional example determine this intended reading; see insight I1
--   - encoding: finite signed weight vectors of variable length, with padding and convolution → canonical real polynomials, with polynomial addition and multiplication and finite coordinate projections; reason: finite coefficient sequences modulo trailing zeros give exactly the same weights, evaluations and finite-dimensional strict exposure tests
--   - encoding: functions on [0,1] and Lebesgue integration → functions on the interval subtype with the pullback of real Lebesgue measure; reason: equality is exactly equality on the source domain and every admissible L2 density remains available
--   - encoding: period t ranges from 1 to T and the terminal family is at T+1 → n<T indexes the update from n to n+1 remaining decisions, with terminal index 0; reason: n=T-t is a bijection between the decision updates; the zero-horizon case contains only the terminal identities
-- source:
--   Hao Zhang, Dynamic Learning and Decision Making via Basis Weight Vectors, Operations Research (2022), DOI 10.1287/opre.2021.2240, supplied PDF p. 17 (printed p. 17), Theorem 1, Eqs. (15)–(16); proof PDF pp. 52–53 (EC pp. 8–9).

import Definitions.Def_BasisWeightLearning_Exact_FunctionRecursion
import Definitions.Def_BasisWeightLearning_Exact_WeightRecursion
import Definitions.Def_BasisWeightLearning_Exact_Policy
open scoped BigOperators

namespace BasisWeightLearning.Exact
theorem theorem_1 {A S : Type} [Fintype A] [Nonempty A] [Fintype S] [Nonempty S]
    (T : ℕ)
    (M : HiddenModel Theta A S) (hM : M.Valid)
    (D : PolynomialData A S) (hA1 : D.Represents M)
    (B : TerminalData) (hA2 : B.Valid) :
    functionStages M B 0 = (B.functions : Set ValueFunction) ∧
    weightStages D M.discount B 0 = B.weight '' (B.functions : Set ValueFunction) ∧
    ∀ n : ℕ, n < T →
      weightStages D M.discount B (n + 1) =
        weightFrontier (⋃ a, weightAction D M.discount (weightStages D M.discount B n) a) ∧
      (∀ a : A,
        weightAction D M.discount (weightStages D M.discount B n) a =
          weightFrontier {w | ∃ next : S → Weight,
            (∀ s, next s ∈ weightStages D M.discount B n) ∧
            w = expectedWeight D a + Polynomial.C M.discount *
              ∑ s, D.probability a s * next s}) ∧
      functionStages M B (n + 1) =
        functionFrontier (evaluate '' weightStages D M.discount B (n + 1)) := by sorry
end BasisWeightLearning.Exact
