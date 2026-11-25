-- Prove2me | Theorems.Thm_DetDLP_M3A_FpPolyDefs_fpEntry_ordinary_vertex
-- name    : DetDLP.M3A.FpPolyDefs.fpEntry_ordinary_vertex
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T05:47:00.480013+00:00
-- url     : https://prove2.me/theorems/5a28aa34-fe5c-40e1-ad02-6c90b73ff9ec
-- title:
--   Finite-field ordinary-vertex entry agreement
-- statement:
--   At each ordinary gate vertex of the subdivided finite-field wire factor graph, fpEntry encodes the exact lifted gate-weight truncated polynomial.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3A_FpArithNet
import Definitions.Def_DetDLP_M3A_FpPolyDefs
import Definitions.Def_DetDLP_W3_IncQueryBounds

set_option autoImplicit false
open DetDLP DetDLP.M3A DetDLP.M3A.FpPolyDefs S8J S8H.PointAddresses

set_option autoImplicit false
open DetDLP DetDLP.M3A DetDLP.M3A.FpPolyDefs S8J S8H.PointAddresses

theorem DetDLP.M3A.FpPolyDefs.fpEntry_ordinary_vertex
    {p m' D K T : ℕ} [Fact p.Prime] (hd : 1 ≤ D)
    (q : w3_Query) (w η : W) (Pval : ℕ) (seed : FpSeed p m')
    (sl : Fin (FpArithNet.layout hd m' K η).ng ≃ (w3_lookupSlot q ⊕ Fin (FpArithNet.arith hd m' K η).ng))
    (addr : (v : Fin (w3_factorGraph (FpArithNet.layout hd m' K η)).nV) →
      (Fin ((w3_factorGraph (FpArithNet.layout hd m' K η)).deg v) → Bool) → ℕ)
    (hP : 0 < w3_precision q)
    (hm : m w = m') (hD : d w = D) (hK : k w = K) (hpre : pre w = η)
    (hpr : prime w = p) (hth : threshold w = T) (htg : target w = Pval) (hlen : len w = w3_len q)
    (hseed : ∀ i : Fin m',
      (nums (field w 1)).getD (2 * i.val) 0 - 1 = (seed i).1.val ∧
      (nums (field w 1)).getD (2 * i.val + 1) 0 = (seed i).2.val)
    (hsl : ∀ g : Fin (FpArithNet.arith hd m' K η).ng, sl (Fin.castAdd (4 * m') g) = .inr g)
    (g : Fin (FpArithNet.arith hd m' K η).ng)
    (a : Fin ((w3_factorGraph (FpArithNet.layout hd m' K η)).subdivision.deg
      ((w3_factorGraph (FpArithNet.layout hd m' K η)).oldVertex
        (Fin.castAdd (FpArithNet.layout hd m' K η).nb (Fin.castAdd (4 * m') g)))) → Bool) :
    let L := FpArithNet.layout hd m' K η
    let G := w3_factorGraph L
    let v := G.oldVertex (Fin.castAdd L.nb (Fin.castAdd (4 * m') g))
    EncodesTruncPoly (w3_precision q) (w3_len q) (fpEntry (encodePortQuery w v.val (List.ofFn a)))
      (w3_liftTensor G (w3_gateWeight (w3_incSlot L sl) addr (w3_factorChecks L (FpArithNet.test hd p T Pval seed η))) v a) := by sorry
