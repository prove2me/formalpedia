-- Prove2me | Theorems.Thm_DetDLP_theorem_1_1_from_appendix_d
-- name    : DetDLP.theorem_1_1_from_appendix_d
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T10:29:12.209148+00:00
-- url     : https://prove2.me/theorems/de5a0a3d-3615-5c54-b970-82a08423d350
-- title:
--   Theorem 1.1. Deterministic discrete logarithms under the Cauchy–Hermite construction
-- statement:
--   Under the cited Appendix D construction, the deterministic machines of Theorem 1.1 solve discrete logarithms in prime-order elliptic curves and in prime finite fields, including the subgroup membership case, uniqueness of the answer and the stated subexponential time and space bounds.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_OpenAIAppendixD
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

open DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.theorem_1_1_from_appendix_d (hOAI : OpenAIAppendixDPremise) :
    (∃ (M_ec : PrimitiveMachine) (out_ec : Fin M_ec.tapeCount) (C_ec : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p →
        ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          letI := ecPointFintype E
          let r := Fintype.card E.toAffine.Point
          r.Prime →
          ∀ (P Q : E.toAffine.Point),
            addOrderOf P = r →
            ∃ x : ℕ, x < r ∧ x • P = Q ∧
              (∀ y : ℕ, y < r → y • P = Q → y = x) ∧
              RunsWithin M_ec out_ec (encodeECDLPInput p E P Q) (countWord x)
                (mainTimeBound C_ec (bitLen p)) (mainSpaceBound C_ec (bitLen p))) ∧
    (∃ (M_fp : PrimitiveMachine) (out_fp : Fin M_fp.tapeCount) (C_fp : ℕ),
      ∀ (p : ℕ) [Fact p.Prime] (g t : (ZMod p)ˣ),
        (t ∉ Subgroup.zpowers g →
          RunsWithin M_fp out_fp (encodeFpDLPInput p (g : ZMod p).val (t : ZMod p).val)
            (encodeOptionNatBin none)
            (mainTimeBound C_fp (bitLen p)) (mainSpaceBound C_fp (bitLen p))) ∧
        (t ∈ Subgroup.zpowers g →
          ∃ x : ℕ, x < orderOf g ∧ g ^ x = t ∧
            (∀ y : ℕ, y < orderOf g → g ^ y = t → y = x) ∧
            RunsWithin M_fp out_fp (encodeFpDLPInput p (g : ZMod p).val (t : ZMod p).val)
              (encodeOptionNatBin (some x))
              (mainTimeBound C_fp (bitLen p)) (mainSpaceBound C_fp (bitLen p)))) := by sorry
