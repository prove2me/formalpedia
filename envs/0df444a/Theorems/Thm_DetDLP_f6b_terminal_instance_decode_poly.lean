-- Prove2me | Theorems.Thm_DetDLP_f6b_terminal_instance_decode_poly
-- name    : DetDLP.f6b_terminal_instance_decode_poly
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T02:44:15.463568+00:00
-- url     : https://prove2.me/theorems/9306278c-584e-46eb-843f-b03862ff5969
-- title:
--   Polynomial-time extraction of terminal BTN kernel metadata
-- statement:
--   The terminal decoder runs in polynomial time on every bit string. On the canonical encoding of a terminal BTN, it returns exactly the descriptor, edge and vertex counts, precision, arity, radix, and endpoint code. Writing $d$ for the ordered list of endpoint indices, the last two fields are
--
--   $$r=|V|+3,\qquad c=r^{2|E|}+\sum_{i=0}^{2|E|-1}d_i r^i.$$
--
--   These are the serialized metadata used by the small contraction kernel; the extraction does not require an edge-count bound.
-- source:
--   Definitions/Def_DetDLP_TerminalBTN.lean, encodeTerminalBTNInstance; Solutions/M14A_small_kernel.lean, endpoint code in theorem solution.

import Definitions.Def_DetDLP_F6B_TerminalDecode
open DetDLP OAI.Algorithms.SubexponentialSAT
set_option autoImplicit false

theorem DetDLP.f6b_terminal_instance_decode_poly : Groundwork.PolyT DetDLP.F6B.decode ∧
    ∀ (desc : List Bool) (G : BipartiteMultigraph) (b m k S P0 ℓ : ℕ)
      (lookupVerts : Finset (Fin G.nV)),
      let r := G.nV + 3
      let pairs := (List.finRange G.nE).map fun e => ((G.endpoints e).1.val,(G.endpoints e).2.val)
      let code := Nat.ofDigits r (pairs.flatMap fun xy => [xy.1,xy.2]) + r^(2*pairs.length)
      DetDLP.F6B.decode (encodeTerminalBTNInstance desc G b m k S P0 ℓ lookupVerts) =
        Encoding.encodeList id [desc,G.nE.bits,G.nV.bits,P0.bits,ℓ.bits,r.bits,code.bits] := by sorry
