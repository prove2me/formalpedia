-- Prove2me | Theorems.Thm_CookPvsNP_unary_to_encNat_stack
-- name    : CookPvsNP.unary_to_encNat_stack
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T21:26:37.993043+00:00
-- url     : https://prove2.me/theorems/a107c390-d71f-4fe3-9b77-cbcc57227cb6
-- title:
--   A finite stack program writes a canonical binary code from a unary counter
-- statement:
--   There are a fixed finite five-stack program and a constant $C$ with the following property. For every natural number $n$ and every output tail $t$, initialize stack 0 to $n$ copies of the symbol $1$, stack 1 to $t$, and the remaining stacks to the empty word. The program halts within
--
--   $$
--   C(n+1)^2
--   $$
--
--   source steps, preserving stack 0, replacing stack 1 by $\operatorname{encNat}(n)\mathbin{++}t$, and leaving the other stacks empty. Here $\operatorname{encNat}$ is the published least-significant-bit-first canonical binary encoding with a trailing separator; for $n=0$ it consists only of that separator. The initial source stack is assumed to be a valid unary counter; the statement does not assert termination on arbitrary malformed source stacks.
-- source:
--   Auxiliary finite-stack implementation for the exact binary tensor encoding in Hillar and Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), arXiv:0911.1393v5, Theorem 1.3 and its proof, pp. 0:20–0:21. This machine-level writer and bound are formalization support, not a theorem explicitly stated in the paper.

import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding
open CookPvsNP ProjSchedTW.Complexity

namespace CookPvsNP

theorem unary_to_encNat_stack :
    ∃ (p : StackProg (Fin 5) BSym) (C : ℕ),
      ∀ (n : ℕ) (tail : List BSym), ∃ steps,
        p.Exec
          (fun k ↦ if k = 0 then List.replicate n .one else if k = 1 then tail else [])
          (fun k ↦ if k = 0 then List.replicate n .one else if k = 1 then encNat n ++ tail else []) steps ∧
        steps ≤ C*(n+1)^2 := by
  sorry

end CookPvsNP
