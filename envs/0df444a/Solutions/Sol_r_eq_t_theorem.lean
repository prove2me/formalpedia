-- Prove2me | solution 1 for r_eq_t_theorem
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:55:56.850064+00:00
-- url     : https://prove2.me/submissions/53337286-4728-404e-ac5f-306cd31fa858

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Theorems.Thm_flt_fermat_last_theorem

/-!
The posted statement is Fermat's Last Theorem for prime exponents `p ≥ 5` with positive,
pairwise coprime `a b c`.  It is the special case `n = p` of the platform theorem
`flt.fermat_last_theorem` (Fermat's Last Theorem for every exponent `n ≥ 3`), which is
Proved on the server.  Only the positivity hypotheses and the equation are needed.
-/

theorem solution (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hac : Nat.Coprime a c)
    (heq : a ^ p + b ^ p = c ^ p) : False :=
  flt.fermat_last_theorem p (by omega) a b c ha hb hc heq
