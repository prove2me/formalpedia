-- Prove2me | Theorems.Thm_DetDLP_m3b_ec_body_fits_core
-- name    : DetDLP.m3b_ec_body_fits_core
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T03:46:41.596983+00:00
-- url     : https://prove2.me/theorems/9151d304-83f9-5679-95d0-7463aecd5a5f
-- title:
--   Anchored EC body FitsCore agreement
-- statement:
--   For any canonical elliptic-curve query input word, the polynomial-time network compiled by ECPolyDefs matches the anchored physical body network ECPhysicalNet.body under ECFits.FitsCore.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3B_ECPhysicalNet
import Definitions.Def_DetDLP_M3B_ECPolyDefs
import Definitions.Def_DetDLP_M3B_ECFits
import Definitions.Def_DetDLP_W3_Separator

set_option autoImplicit false
open DetDLP DetDLP.M3B OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

set_option autoImplicit false
open DetDLP DetDLP.M3B OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m3b_ec_body_fits_core
    (p : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (ha₁ : E.a₁ = 0) (ha₂ : E.a₂ = 0) (ha₃ : E.a₃ = 0) (hp : 67 < p) :
    letI := ecPointFintype E
    let M := Fintype.card E.toAffine.Point
    let b := bitLen p
    let m := blockCount b
    let T := hashThreshold p (M - 1) m M
    let k := Nat.clog 2 (2 * T)
    64 ≤ M → 4096 * m ≤ M - 1 →
    ∀ (seed : ECSeed p m) (F : Fin m → List E.toAffine.Point) (P : E.toAffine.Point)
      (y : w3_Label M (IndexedFactorBase.mk F).totalCoords) (pre : List Bool),
      let input := Encoding.encodeList id
        [encodeCurveInput p E, encodeNatListBin (pointCoords P), encodeNatListBin [M, T],
         encodeNatListBin ((List.finRange m).flatMap fun i =>
           [(seed i false).1.val + 1, (seed i false).2.val, (seed i true).1.val + 1, (seed i true).2.val]),
         encodeECFactorBlocks F, encodeNatListBin (List.ofFn fun j => (y j).val), pre]
      ECFits.FitsCore (ECPolyDefs.compiled input) (ECPhysicalNet.body (k := k) E seed T P pre) := by sorry
