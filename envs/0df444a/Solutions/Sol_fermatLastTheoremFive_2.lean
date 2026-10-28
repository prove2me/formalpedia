-- Prove2me | solution 2 for fermatLastTheoremFive
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-25T19:30:01.507233+00:00
-- url     : https://prove2.me/submissions/14dd4189-216c-498c-89af-bb8e7fe6c6ae

import Mathlib.NumberTheory.FLT.Basic
import Theorems.Thm_FreyPackage_fermatLastTheoremFor_of_five_le

-- Shorter proof of FLT for n = 5: a direct citation of the already-Proved
-- general theorem for prime exponents >= 5, replacing the 1,999-line
-- bespoke Zphi development currently accepted for fermatLastTheoremFive.
theorem solution : FermatLastTheoremFor 5 :=
  FreyPackage.fermatLastTheoremFor_of_five_le 5 (by decide) le_rfl
