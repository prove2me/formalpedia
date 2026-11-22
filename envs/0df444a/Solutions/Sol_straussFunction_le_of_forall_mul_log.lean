-- Prove2me | solution 1 for straussFunction_le_of_forall_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:54:29.723595+00:00
-- url     : https://prove2.me/submissions/22bd3641-74ac-4bb4-8939-3e5c2f554df3

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
import Theorems.Thm_straussFunction_isLittleO

set_option autoImplicit true
open Finset
open Asymptotics Filter
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, straussFunction k ≤ (3 + ε) * k * Real.log k := by
  obtain ⟨f, hf, hfbound⟩ := straussFunction_isLittleO
  rw [isLittleO_one_iff] at hf
  filter_upwards [hf.eventually_le_const hε, eventually_ge_atTop 4] with k hk hk4
  grw [hfbound k hk4, hk]
