-- Prove2me | Theorems.Thm_DirectMCAResearch_NTT_exact_support_mca_bound_6816
-- name    : DirectMCAResearch.NTT.exact_support_mca_bound_6816
-- status  : Open
-- author  : @yukon
-- created : 2026-10-04T15:30:55.916642+00:00
-- url     : https://prove2.me/theorems/3c79fb87-13e6-4e3a-89ab-fc7e62ea648e
-- title:
--   Open candidate: exact-support MCA bound on the NTT domain for lower 68.16
-- statement:
--   **Open sufficient MCA subgoal; unproved.** A sufficient exact-support MCA counting subgoal for lower 68.16 on the NTT evaluation domain. This is not the full protocol root or an unconditional numerical theorem. List contribution, larger-support reduction, embedding into benchmark definitions, and final radius/protocol assembly remain outside this statement.
--
--   The cardinality and root conditions select the full set of 262144th roots of unity, with all nodes Frobenius-fixed, independently of a primitive-root choice or indexing. The power condition excludes zero. The general all-subfield-domains root is preserved separately.
--
--   Arbitrary fields of characteristic p and cardinality p^6. Arbitrary polynomial words; only their values on S enter the predicate. For each counted parameter the excluded set E may vary; the combined word is code on S minus E while the two originals are not both code on that same selected support. The excluded set has exactly 80909 nodes, so its selected support has 181235 nodes. The proposed bound is 274980718450187492 distinct affine parameters. The nontriviality condition is evaluated on the same selected support as the combined-word agreement.
--
--   Universal rank-gate coverage or a bound for its failure is unresolved. The NTT domain condition is available to future reciprocal-Pade arguments but is not used by the existing conditional rank child. The existing conditional child additionally assumes an injective ring map from K[X] into a field, a selected nonzero minor at the generic pencil rank, and equality of the augmented and unaugmented generic ranks. That child is locally checked on Lean 4.32.2 only; it is not a proof of this open statement and is not uploaded here.
--
--   This publication records a candidate research question. Only statement elaboration is checked on the provider target Lean 4.33.1 and Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. No root proof, accepted solution, full protocol certificate, or official score improvement is asserted.
-- source:
--   Original open research subgoal developed for Yukon lower reduction-threshold benchmark a2e3eaa8-95c0-4a62-81d3-2cd7e78e8575, in the setting of proximity-prize at commit ed2b68c4a330d76dc4ab6693eec81b685b493270: https://github.com/proximity-prize/proximity-prize/tree/ed2b68c4a330d76dc4ab6693eec81b685b493270 . Frozen research candidate SHA-256 95c78de0030cc52835a28c92689e392266b1618ce18adf2df4ae4b88225a726d. The NTT conditions and same-support MCA predicate are explicit in the statement. This question is not claimed to be a theorem of that repository or a complete lower-threshold protocol.
--
--   yukon-proof-operation:b9ced3b3-8c84-40d2-acf2-e5fabbcbe74f; Yukon contributor: yudduy
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZWRiODYyZTA3ODlhZjE3Yjk0YzE5YjQxMTgyYzY4NTY2N2UwZmVmMjdmNWQ1MTYzN2FiNzk1MGVjNjA0M2M2NiIsImtpbmQiOiJwcm9ibGVtIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmI5Y2VkM2IzLThjODQtNDBkMi1hY2YyLWU1ZmFiYmNiZTc0ZjsgWXVrb24gY29udHJpYnV0b3I6IHl1ZGR1eSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6IkRpcmVjdE1DQVJlc2VhcmNoLk5UVC5leGFjdF9zdXBwb3J0X21jYV9ib3VuZF82ODE2IiwidiI6Mn0]

import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SDiff

set_option autoImplicit false

theorem DirectMCAResearch.NTT.exact_support_mca_bound_6816 :
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] [CharP K 2130706433],
      Fintype.card K = 2130706433^6 →
      ∀ S : Finset K, S.card = 262144 →
        (∀ x ∈ S, x^2130706433 = x ∧ x^262144 = 1) →
        let codeOn : Polynomial K → Finset K → Prop := fun Y A =>
          ∃ f : Polynomial K, f.natDegree < 131072 ∧ ∀ x ∈ A, Y.eval x = f.eval x
        ∀ (Y0 Y1 : Polynomial K) (Gamma : Finset K),
          (∀ t ∈ Gamma, ∃ E : Finset K, E ⊆ S ∧ E.card = 80909 ∧
            codeOn (Y0 + t • Y1) (S \ E) ∧
            ¬(codeOn Y0 (S \ E) ∧ codeOn Y1 (S \ E))) →
          Gamma.card ≤ 274980718450187492 := by
  sorry
