-- Prove2me | Theorems.Thm_DetDLP_packed_scalar_leaf_contraction_scan
-- name    : DetDLP.packed_scalar_leaf_contraction_scan
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T16:04:15.974808+00:00
-- url     : https://prove2.me/theorems/1b48c2f8-a1de-472b-aece-a7dd51e94b66
-- title:
--   Exact bounded-width integer scan for scalar contraction leaves
-- statement:
--   Enumerate edge assignments by the bits of a binary counter, visiting original vertex ports in their canonical order. Pack the coefficients of each tensor entry into a single positive radix. The sum of the integer products recovers the exact low coefficients of the original integer polynomial contraction and their canonical output word modulo 2^P. The theorem supplies a uniform bound on the bit length of every partial sum and on the value of every partial vertex product, so even a full exhaustive scan at a leaf has polynomial arithmetic workspace.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Section 5.2, direct summation for small-scale instances and recursion leaves.

import Definitions.Def_DetDLP_BTN

set_option autoImplicit false
open Finset

namespace DetDLP

theorem packed_scalar_leaf_contraction_scan {ell : ℕ} (G : BipartiteMultigraph) (P : ℕ)
    (A : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→Fin ell→ℕ) (ha : ∀ v t i,A v t i<2^P) :
    let W := G.nE+G.nV*(P+Nat.clog 2 ell)+1+P
    let b := 2^W
    let factor (k : ℕ) (v : Fin G.nV) := Nat.ofDigits b (List.ofFn
      (A v (fun j => k.testBit ((G.ports v).get j).val)))
    let total (n : ℕ) := ∑ k∈range n,∏ v,factor k v
    let F := BTNContract G (fun v t => ∑ i : Fin ell,Polynomial.monomial i.val (A v t i:ℤ))
    (encodeNatListBin (List.ofFn fun i : Fin ell => total (2^G.nE)/b^i.val%b%(2^P)) =
      encodeNatListBin (List.ofFn fun i : Fin ell => (F.coeff i.val:ZMod (2^P)).val)) ∧
    (∀ n,n≤2^G.nE→(total n).size≤G.nE+W*(ell*G.nV)+1) ∧
    (∀ k (vs : Finset (Fin G.nV)),(∏ v∈vs,factor k v)≤b^(ell*G.nV)) := by sorry

end DetDLP
