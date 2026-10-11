-- Prove2me | Theorems.Thm_Algo2Lean_Fibonacci_Run_amortized
-- name    : Algo2Lean.Fibonacci.Run.amortized
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:53:06.999057+00:00
-- url     : https://prove2.me/theorems/09459664-7d31-4244-b303-390d7405127c
-- title:
--   Fibonacci heap: amortized running time for arbitrary operation sequences
-- statement:
--   For a valid pure `Run` with degree parameter D, u updates, e extractions, total modeled work W, and before/after counts, scaled potential Ψ satisfies
--
--   $$W+\Psi(\mathrm{after})\leq\Psi(\mathrm{before})+20u+12(D+1)e.$$
--
--   This model-level theorem allows arbitrary mixtures of its valid operations and nonzero initial potential. It is distinct from a theorem about arbitrary unvalidated compiled transcripts; the compiled queue contracts provide that connection for algorithm clients.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/Fibonacci.lean#L384-L395

import Definitions.Def_Algo2LeanLib_Fibonacci
import Theorems.Thm_Algo2Lean_Fibonacci_Decrease_amortized

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem Algo2Lean.Fibonacci.Run.amortized :
    ∀ {maximumDegree work updates extractions : Nat} {before after : Algo2Lean.Fibonacci.Counts},
      Algo2Lean.Fibonacci.Run maximumDegree before after work updates extractions →
        LE.le.{0} (HAdd.hAdd.{0, 0, 0} work (Algo2Lean.Fibonacci.scaledPotential after))
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0} (Algo2Lean.Fibonacci.scaledPotential before)
              (HMul.hMul.{0, 0, 0} (20 : Nat) updates))
            (HMul.hMul.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} (12 : Nat) (HAdd.hAdd.{0, 0, 0} maximumDegree (1 : Nat)))
              extractions)) := by
  sorry
