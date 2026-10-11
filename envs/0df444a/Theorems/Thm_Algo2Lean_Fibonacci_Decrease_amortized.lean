-- Prove2me | Theorems.Thm_Algo2Lean_Fibonacci_Decrease_amortized
-- name    : Algo2Lean.Fibonacci.Decrease.amortized
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:39:18.472398+00:00
-- url     : https://prove2.me/theorems/47c2c1fc-b513-4d5e-b4e9-5af0c5a3bf27
-- title:
--   Fibonacci heap: constant amortized decrease accounting
-- statement:
--   For any `Decrease before after cuts` in the pure counting model, with potential Φ equal to the model's root/mark potential,
--
--   $$\mathrm{cuts}+\Phi(\mathrm{after})\leq\Phi(\mathrm{before})+4.$$
--
--   The count relation describes a valid decrease. This lemma is independent of generated code and is later scaled to cover the chosen source clocks.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/Fibonacci.lean#L226-L231

import Definitions.Def_Algo2LeanLib_Fibonacci

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem Algo2Lean.Fibonacci.Decrease.amortized :
    ∀ {before after : Algo2Lean.Fibonacci.Counts} {cuts : Nat},
      Algo2Lean.Fibonacci.Decrease before after cuts →
        LE.le.{0} (HAdd.hAdd.{0, 0, 0} cuts (Algo2Lean.Fibonacci.potential after))
          (HAdd.hAdd.{0, 0, 0} (Algo2Lean.Fibonacci.potential before) (4 : Nat)) := by
  sorry
