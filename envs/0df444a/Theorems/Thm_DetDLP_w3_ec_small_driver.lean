-- Prove2me | Theorems.Thm_DetDLP_w3_ec_small_driver
-- name    : DetDLP.w3_ec_small_driver
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T00:43:04.275502+00:00
-- url     : https://prove2.me/theorems/92de1074-aa64-40da-8271-0a82e659cef4
-- title:
--   Physical canonical exponent scan in the small elliptic-curve regime
-- statement:
--   For every elliptic curve of characteristic above three in the small-instance regime, one primitive machine on the prescribed binary curve and point encoding outputs the first exponent taking a full-order generator to the target. A single constant bounds time and visited space uniformly, including when either encoded point is the identity.
-- source:
--   Deterministic Discrete Logarithms, §4.1–4.3, equations (4.1)–(4.5) and proof of Theorem 1.1, pp. 13–16; referee revisions R1 and R2.

import Definitions.Def_DetDLP_W3_Driver
import Definitions.Def_DetDLP_PolyTBridge
set_option autoImplicit false
open DetDLP
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.w3_ec_small_driver : ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (C : ℕ),
    ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
      letI := ecPointFintype E; let M := Fintype.card E.toAffine.Point
      ∀ P Q : E.toAffine.Point, addOrderOf P = M → ¬w3_large p M →
      w3_scanOutput M P Q (fun u => RunsWithin D out (encodeECDLPInput p E P Q) (countWord u)
        (mainTimeBound C (bitLen p)) (mainSpaceBound C (bitLen p))) := by sorry
