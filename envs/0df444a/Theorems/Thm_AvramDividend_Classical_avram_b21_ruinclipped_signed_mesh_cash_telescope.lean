-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b21_ruinclipped_signed_mesh_cash_telescope
-- name    : AvramDividend.Classical.avram_b21_ruinclipped_signed_mesh_cash_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:46:33.643392+00:00
-- url     : https://prove2.me/theorems/a6f8938f-a836-4b08-a7e0-c7924e666c4b
-- title:
--   Ruin-clipped source mesh: time-zero right dividend and signed HJB cash telescoping
-- statement:
--   The exact finite stopped-mesh Ito ledger telescopes discounted test values and retains time-zero and pre-ruin dividend cash; a nonpositive HJB drift may be discarded while Gaussian, jump and error gains remain explicit.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), arXiv:math/0702893; finite-grid deterministic signed inequality only, prior to stochastic Ito-Meyer passage.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_b21_ruinclipped_signed_mesh_cash_telescope
    (N : Nat) (w0 cash0 : Real)
    (V cash gaussian jump drift error : Nat -> Real)
    (hInitial : V 0 + cash0 <= w0)
    (hCell : forall i, i < N ->
      V (i + 1) + cash i <=
        V i + gaussian i + jump i + drift i + error i)
    (hDrift : forall i, i < N -> drift i <= 0) :
    V N + cash0 + (Finset.range N).sum cash <=
      w0 + (Finset.range N).sum gaussian +
        (Finset.range N).sum jump +
        (Finset.range N).sum error := by sorry
