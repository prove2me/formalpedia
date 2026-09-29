-- Prove2me | solution 1 for flt5_probe_nf_cyc_pid
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T02:34:33.775874+00:00
-- url     : https://prove2.me/submissions/2f86e3b2-5b86-45dc-9c31-93f50503ec40

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

theorem solution (a b : ℤ) : a + b = b + a := add_comm a b
