-- Prove2me | Theorems.Thm_DetDLP_M3A_FpPolyDefs_fpEntry_lookup_vertex_v2
-- name    : DetDLP.M3A.FpPolyDefs.fpEntry_lookup_vertex_v2
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T04:41:32.666318+00:00
-- url     : https://prove2.me/theorems/bd068d0c-6ce8-425f-9f57-cf5256486779
-- title:
--   Finite-field lookup-vertex entry agreement (ECLayout.test)
-- statement:
--   At each lookup vertex of the subdivided finite-field wire factor graph under ECLayout.test, fpEntry encodes the exact lifted gate-weight truncated polynomial.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3A_FpPolyDefs
import Definitions.Def_DetDLP_M3B_ECLayout
import Definitions.Def_DetDLP_W3_IncQueryBounds

set_option autoImplicit false
open DetDLP DetDLP.M3A DetDLP.M3A.FpPolyDefs S8J S8H.PointAddresses

set_option autoImplicit false
open DetDLP DetDLP.M3A DetDLP.M3A.FpPolyDefs S8J S8H.PointAddresses

theorem DetDLP.M3A.FpPolyDefs.fpEntry_lookup_vertex_v2
    (q : w3_Query) (w : W) (A : w3_FactorLayout) (bus : Fin (4 * q.m) → Fin q.k → Fin A.nb)
    (t : w3_factorTest A)
    (sl : Fin (M3B.ECLayout.layout A bus).ng ≃ (w3_lookupSlot q ⊕ Fin A.ng))
    (addr : (v : Fin (w3_factorGraph (M3B.ECLayout.layout A bus)).nV) →
      (Fin ((w3_factorGraph (M3B.ECLayout.layout A bus)).deg v) → Bool) → ℕ)
    (hm : m w = q.m) (hp : prec w = w3_precision q) (hn : len w = w3_len q)
    (hng : (whole (m w) (d w) (k w) (pre w).length).ng = A.ng + 4 * q.m)
    (s : Fin (4 * q.m)) (blk : Fin q.m) (crd : Fin 2)
    (hblk : s.val % q.m = blk.val)
    (hsl : sl (Fin.natAdd A.ng s) = .inl (blk, crd, decide (2 * q.m ≤ s.val)))
    (haddr : ∀ values, addr (M3B.ECLayout.vertex A bus s) values =
      bitsToNat (fun j : Fin q.k => values (M3B.ECLayout.port A bus s j)))
    (hl : ((blocks w).getD blk.val []).length = (q.FB.blocks blk).length)
    (hash : ℕ → ℕ)
    (hc : ∀ x, hash x = ((nums (field w 1)).getD (2 * blk.val) 0 * x + (nums (field w 1)).getD (2 * blk.val + 1) 0) % prime w)
    (ha : ∀ r : Fin (q.FB.blocks blk).length, hash (((blocks w).getD blk.val []).getD r.val 0) = q.addr blk r)
    (hy : ∀ r : Fin (q.FB.blocks blk).length,
      num (field w 3) ((((blocks w).take blk.val).map List.length).sum + r.val) = (q.y (q.FB.coordOf blk r)).val)
    (inj : Function.Injective (q.addr blk))
    (a : Fin ((w3_factorGraph (M3B.ECLayout.layout A bus)).subdivision.deg
      ((w3_factorGraph (M3B.ECLayout.layout A bus)).oldVertex (M3B.ECLayout.vertex A bus s))) → Bool) :
    let G := w3_factorGraph (M3B.ECLayout.layout A bus)
    let v := G.oldVertex (M3B.ECLayout.vertex A bus s)
    EncodesTruncPoly (w3_precision q) (w3_len q) (fpEntry (encodePortQuery w v.val (List.ofFn a)))
      (w3_liftTensor G (w3_gateWeight (w3_incSlot (M3B.ECLayout.layout A bus) sl) addr (w3_factorChecks _ (M3B.ECLayout.test A bus t))) v a) := by sorry
