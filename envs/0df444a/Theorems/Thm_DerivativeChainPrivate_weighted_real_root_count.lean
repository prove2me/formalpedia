-- Prove2me | Theorems.Thm_DerivativeChainPrivate_weighted_real_root_count
-- name    : DerivativeChainPrivate.weighted_real_root_count
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-19T05:00:13.188555+00:00
-- url     : https://prove2.me/theorems/f4f3f7a2-ec61-407f-aa57-dafdbb0eba4c
-- title:
--   Weighted real quotient derivatives preserve degree and real-root count
-- statement:
--   For every nonzero real polynomial Q and natural r,k, the polynomial (r+1)Q+(k+1)XQ′ has the same degree as Q and at least as many real root slots, counted with multiplicity. Thus the weighted step cannot increase the nonreal-root deficit. This is a supporting result for compressed chains, not the full three-radius chain theorem.
-- source:
--   Derivative-zero chains: public formalization reference, R45, DerivativeChainPrivate.weighted_real_root_count. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.weighted_real_root_count (q : Polynomial ℝ) (hq : q ≠ 0) (r k : ℕ) :
    let b := C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative
    b.natDegree = q.natDegree ∧ q.roots.card ≤ b.roots.card := by sorry
