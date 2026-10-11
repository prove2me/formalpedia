-- Prove2me | Theorems.Thm_Algo2Lean_Fibonacci_degree_logarithmic
-- name    : Algo2Lean.Fibonacci.degree_logarithmic
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:51:35.797661+00:00
-- url     : https://prove2.me/theorems/9daa1e58-a2a8-421c-9d8a-2a8bd36561ea
-- title:
--   Fibonacci heap: logarithmic degree bound
-- statement:
--   Let d and n be natural numbers. If the minimum subtree size required for degree d is at most n, then
--
--   $$d\leq 2\lfloor\log_2 n\rfloor+1.$$
--
--   Here Lean's `Nat.log2` is zero at zero. This integer bound is the degree estimate used in the heap's running-time proof. It corresponds to the Fibonacci-heap size/degree argument in CLRS's online Fibonacci-heap supplement (retained third-edition §19.4, Corollary 19.5).
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/Fibonacci.lean#L63-L72

import Definitions.Def_Algo2LeanLib_Fibonacci

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem Algo2Lean.Fibonacci.degree_logarithmic :
    ∀ {degree nodes : Nat},
      LE.le.{0} (Algo2Lean.Fibonacci.minimumNodes degree) nodes →
        LE.le.{0} degree (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) nodes.log2) (1 : Nat)) := by
  sorry
