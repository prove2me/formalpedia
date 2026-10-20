-- Prove2me | Theorems.Thm_DerivativeChainPrivate_endpoint_deficit
-- name    : DerivativeChainPrivate.endpoint_deficit
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-17T03:08:26.873456+00:00
-- url     : https://prove2.me/theorems/8c99686f-4cd1-4f74-830a-f23406048c4a
-- title:
--   Strict finite endpoint deficit implication
-- statement:
--   Let I be a finite type. Let w,D,B be real-valued functions on I, with w_i and D_i nonnegative, and let C,E be arbitrary real numbers. If
--
--   $$\sum_i w_iD_i^2\le E<\sum_i w_i\max(C-B_i,0)^2,$$
--
--   then there is an i with D_i+B_i<C. The conclusion is strict. Weights need not sum to one. For an empty I the hypotheses are inconsistent. This scalar implication does not establish these hypotheses for arbitrary derivative towers.
-- source:
--   Derivative-zero chains: public formalization reference, R12, DerivativeChainPrivate.endpoint_deficit. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem DerivativeChainPrivate.endpoint_deficit {ι : Type*} [Fintype ι]
    (w D B : ι → ℝ) (C E : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hD : ∀ i, 0 ≤ D i)
    (henergy : (∑ i, w i * (D i) ^ 2) ≤ E)
    (hdeficit : E < ∑ i, w i * (max (C - B i) 0) ^ 2) :
    ∃ i, D i + B i < C  := by sorry
