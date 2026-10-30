-- Prove2me | Theorems.Thm_ExponomialAssortment_FPTAS_cardinality_fptas
-- name    : ExponomialAssortment.FPTAS.cardinality_fptas
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T21:16:13.505475+00:00
-- url     : https://prove2.me/theorems/f58212da-ce3c-4c28-8e3a-dc474ebb1886
-- title:
--   Cardinality-constrained exponomial assortment FPTAS
-- statement:
--   There is one algorithm and one fixed polynomial which, for every finite rational input and positive rational requested accuracy, return a feasible assortment with true revenue at least 1−ε times optimum in time polynomial in binary input length and 1/ε. The unrestricted real semantic specification and the full printed internal fourth-power guarantee are retained. The computational output follows the rounded and pruned scheme, enumerating all first-product guesses.
--
--   Differences from the source:
--   - encoding: one-based indicators and normalized utilities → Fin n, finite selected sets, Valid and Feasible with 1 ≤ C ≤ n; reason: equivalent indexing and the cardinality extension explicitly asserted in §8, counting the outside option; C=n recovers the unconstrained setting
--   - encoding: rounded averages and objectives treated as defined → partial rounding graphs with existence in conclusions; reason: the printed grid has no ceiling on some legal inputs; preserving asserted definedness exposes I1 without adding a hypothesis or endpoint
--   - encoding: FPTAS for arbitrary normalized real instances and polynomial time in finite input size → real semantic specification plus uniform binary machine on rational data and accuracy; reason: separates mathematical semantics from finite numerical representation without an exact-real oracle
--   - encoding: accuracy η in the internal fourth-power guarantee and requested ε in the FPTAS → the full internal guarantee and the headline guarantee, choosing η=ε/4 when ε<1; reason: preserves the printed internal claim, while the chosen accuracy converts it to 1−ε; ε≥1, C=1 and zero prices use the outside-only assortment
--   - encoding: λ>0 and arbitrary translated/relabelled utilities normalize to λ=1 and u_n=0 → an explicit normalization correspondence and encoded relabelling; reason: §2.2 states these probability-preserving transformations
-- source:
--   Aouad, Feldman and Segev (2023), DOI 10.1287/mnsc.2022.4492, published repository manuscript, §1.1 printed p. 4 / PDF 5; §5.3 printed p. 19 / PDF 20; §8 printed p. 30 / PDF 31

import Definitions.Def_ExponomialAssortment_FPTAS_Computation

namespace ExponomialAssortment.FPTAS

theorem cardinality_fptas :
    Normalization ∧
    (∀ (n : ℕ) (I : Instance n), Valid I → ∀ C, 1 ≤ C → C ≤ n →
      ∀ η : ℝ, 0 < η → (∃ i, 0 < I.price i) →
      ∀ l f, bestSingle I η l →
      ∀ T w, RoundedOptimal I C η true T w → firstProduct I T f →
      ∀ S v, PrunedOptimal I C η l f S v →
      ∀ O, Optimal I C O → (1 - η)^4 * revenue I O ≤ revenue I S) ∧
    (∀ (n : ℕ) (I : Instance n), Valid I → ∀ C, 1 ≤ C → C ≤ n →
      ∀ ε : ℝ, 0 < ε → ∃ S, SchemeOutput I C ε S ∧ RevenueGuarantee I C ε S) ∧
    ∃ (M : BinaryMachine) (c d : ℕ), 0 < c ∧ ∀ q : RationalInput,
      InputValid q → ∃ (S : Finset (Fin q.n)) (t : ℕ),
        MachineRuns M (encodeInput q) (encodeSet S) t ∧ t ≤ HeadlineBound c d q ∧
        EncodedSchemeOutput q S ∧ q.outside ∈ S ∧ S.card ≤ q.capacity ∧
        ∀ T : Finset (Fin q.n), q.outside ∈ T → T.card ≤ q.capacity →
          (1 - (q.accuracy : ℝ)) * inputRevenue q T ≤ inputRevenue q S ∧
          ((q.accuracy : ℝ) < 1 →
            (1 - (q.accuracy : ℝ) / 4)^4 * inputRevenue q T ≤ inputRevenue q S) := by sorry

end ExponomialAssortment.FPTAS
