-- Prove2me | Theorems.Thm_DetDLP_s8n_ec_moment_signal_addresses
-- name    : DetDLP.s8n_ec_moment_signal_addresses
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T11:54:57.672804+00:00
-- url     : https://prove2.me/theorems/f74b01f2-c50c-4a85-b2e4-f000417344b4
-- title:
--   Uniform source addressing for the elliptic-curve moment circuit
-- statement:
--   A single polynomial-time function on an encoded query and incidence index returns the actual register read by that incidence. It covers every moment tag index, elliptic-curve input and prefix in the physical seed, arithmetic and point-addition circuits.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8N_Routes_v3

set_option autoImplicit false
open DetDLP DetDLP.S8N DetDLP.S8H0 RegisterMap NamedBlocks
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.s8n_ec_moment_signal_addresses :
    ∃ signal : List Bool → ℕ → ℕ,
      Groundwork.PolyT (fun z : List Bool × ℕ => signal z.1 z.2) ∧
      ∀ (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
        (hm : 1 ≤ blockCount (bitLen p)) (j : Fin 4) (T : ℕ) (η : List Bool),
        let m := blockCount (bitLen p)
        let s := RoutesV2.bank j m (GateSemantics.d p) (GateSemantics.e p)
        let N := joinB (PointGraph.zeroLast s.size)
          (RoutesV2.network (GateSemantics.hd p) hm p T (GateSemantics.coeff E) E.b₂.val
            (-1 : ZMod p).val (3 : ZMod p).val (-27 * E.c₄).val j η id)
        ∀ i : Fin (AnchoredLayout.block N.core (s.size+1)).A.ne,
          signal (M89S1.queryWord 2 (encodeCurveInput p E) [countWord j.val,countWord T,η]) i.val =
            ((AnchoredLayout.wiring N.core N.name).signal i).val := by sorry
