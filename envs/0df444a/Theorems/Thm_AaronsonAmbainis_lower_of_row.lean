-- Prove2me | Theorems.Thm_AaronsonAmbainis_lower_of_row
-- name    : AaronsonAmbainis.lower_of_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:25:48.151193+00:00
-- url     : https://prove2.me/theorems/b635d330-43ec-4ff7-8af1-d35cfd4dcb3f
-- title:
--   Aaronson Ambainis: lower of row
-- statement:
--   Step 3 of the proof of Lemma 4.2 of the paper: if `y` is a row at `u'`, `g u' = false`,
--   `g (u'^G) = true` and `D * y j ≤ ℓ j` on `G`, then `D ≤ ℓ(G)`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Antipodal.lean#L70-L79
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Antipodal.lean#L70-L79

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Antipodal
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]

theorem AaronsonAmbainis.lower_of_row {g : Cube ι → Bool} {u' : Cube ι} {y ℓ : ι → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hy : IsRow g u' y) (hu' : g u' = false) (G : Finset ι)
    (hG : ∀ j ∈ G, D * y j ≤ ℓ j) (hgG : g (flipSet u' G) = true) :
    D ≤ ∑ j ∈ G, ℓ j := by sorry
