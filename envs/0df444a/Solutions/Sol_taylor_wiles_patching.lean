-- Prove2me | solution 1 for taylor_wiles_patching
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:53:30.187288+00:00
-- url     : https://prove2.me/submissions/17e629ae-49aa-424c-8077-b92b4f433dd0

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Theorems.Thm_fermat_last_theorem

theorem solution (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hac : Nat.Coprime a c) (heq : a ^ p + b ^ p = c ^ p) : False :=
  fermat_last_theorem p (by omega) a b c ha hb hc heq
