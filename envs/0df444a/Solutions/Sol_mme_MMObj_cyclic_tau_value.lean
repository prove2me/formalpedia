-- Prove2me | solution 1 for mme_MMObj_cyclic_tau_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:12:26.218628+00:00
-- url     : https://prove2.me/submissions/3045aa9e-e260-4084-a158-0f21059722b4

import Mathlib.Tactic
import Definitions.Def_mme_CW_coupled_value
import Theorems.Thm_mme_MMObj_cyclicSymmetrization_iso
import Theorems.Thm_mme_MMObj_tau_value
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (n m p : ℕ) (tau : ℝ) :
    HasTauValueAtLeast (cyclicSymmetrization (MMObj K n m p)) tau
      ((((n * m * p) * (n * m * p) * (n * m * p) : ℕ) : ℝ) ^ tau) := by
  exact mme_HasTauValueAtLeast_mono_restrict
    (mme_MMObj_cyclicSymmetrization_iso (K := K) n m p).2
    (mme_MMObj_tau_value (K := K)
      (n * m * p) (n * m * p) (n * m * p) tau)
