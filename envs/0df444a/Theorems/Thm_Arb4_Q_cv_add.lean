-- Prove2me | Theorems.Thm_Arb4_Q_cv_add
-- name    : Arb4.Q.cv_add
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:30:49.639626+00:00
-- url     : https://prove2.me/theorems/c5a9f3ef-8054-477a-b681-dacc11cc35ac
-- title:
--   Real value of rational addition
-- statement:
--   Let $a,b$ be stored rationals with real values $x,y$. Then the defined rational addition satisfies $$\operatorname{val}(a\mathbin{+_{Q}}b)=x+y.$$ This transports the exact rational operation to the reals.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Arb4_Q.lean#L197-L198

import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Mathlib
/-  Arb4_Q.lean -- lane Arb4 (h1000 compaction): exact rational arithmetic for Boolean kernel
    checkers.

    A certificate side condition such as the error budget of an octant piece is a polynomial
    inequality between explicit rationals.  Closing it by `norm_num` stores the whole normalisation
    trace in the olean (about 300 KB per budget at height 1000).  Here the same inequality is
    computed by `decide +kernel` over plain `Int`/`Nat` arithmetic (GMP-accelerated literals) and
    transported to `ℝ` by ONE soundness theorem per operation, proved once:

      * `Q`             -- an UNNORMALISED rational `n / (dm + 1)` (`n : ℤ`, `dm : ℕ`): the
                           denominator is positive by construction, so no positivity bookkeeping;
                           `val` is its real value, `frac n d` the rational `n / d` (`d ≥ 1`);
      * `add sub mul neg qabs npow div sumQ` -- the operations, `val_*` their homomorphism laws;
      * `le lt`         -- the Boolean comparisons, `le_sound`, `lt_sound`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/


section
namespace Arb4
end Arb4
open Arb4



section
namespace Arb4.Q
end Arb4.Q
open Arb4.Q





























/-! ## The value homomorphism -/





























/-! ## The comparisons -/











/-! ## Literal conversions (small proof terms for the generated certificates) -/

theorem Arb4.Q.cv_add (a b : Q) (x y : ℝ) (ha : a.val = x) (hb : b.val = y) : (add a b).val = x + y := by sorry
