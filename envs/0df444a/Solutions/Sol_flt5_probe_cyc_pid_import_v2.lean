-- Prove2me | solution 1 for flt5_probe_cyc_pid_import_v2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T02:42:47.300334+00:00
-- url     : https://prove2.me/submissions/94aaf59f-73d3-45de-878a-714c24c6037f

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

theorem solution (a b : ℤ) : a + b = b + a := add_comm a b
