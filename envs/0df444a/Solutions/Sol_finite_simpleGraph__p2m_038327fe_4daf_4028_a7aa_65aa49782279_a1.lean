-- Prove2me | solution 1 for finite_simpleGraph__p2m_038327fe_4daf_4028_a7aa_65aa49782279_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:44:10.682932+00:00
-- url     : https://prove2.me/submissions/3058e28f-e344-4e0a-b793-090ea790d2f4

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] : Finite (SimpleGraph V) := by
  infer_instance