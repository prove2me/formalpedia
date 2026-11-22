-- Prove2me | solution 1 for gcd_coprime_of_gcd_abc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:50:38.601972+00:00
-- url     : https://prove2.me/submissions/3228df1c-ee81-4732-939e-6b67976b7e6d

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Definitions.Def_Polychromatic_FourThree_Combi_CaseTwo
import Definitions.Def_Polychromatic_FourThree_Combi

set_option autoImplicit true
open Finset Pointwise
theorem _root_.solution {a b c : ℤ} {m : ℕ}
    (hm : (m : ℤ) = c - a + b) (hgcd : Finset.gcd {a, b, c} id = 1) :
    (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) = 1 := by
  set d := (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) with hd_def
  -- d divides b, (b-a), and m (lifted to ℤ)
  have hd_b : (d : ℤ) ∣ b := Int.natCast_dvd.mpr
    ((Nat.gcd_dvd_left _ (Nat.gcd _ _)).trans (Nat.gcd_dvd_left _ _))
  have hd_m : (d : ℤ) ∣ ↑m := Int.natCast_dvd_natCast.mpr
    ((Nat.gcd_dvd_left _ (Nat.gcd _ _)).trans (Nat.gcd_dvd_right _ _))
  have hd_ba : (d : ℤ) ∣ (b - a) := Int.natCast_dvd.mpr
    ((Nat.gcd_dvd_right (Nat.gcd _ _) _).trans (Nat.gcd_dvd_left _ _))
  -- d | a and d | c follow from d | b, d | (b-a), d | m
  have hd_a : (d : ℤ) ∣ a := by
    have : a = b - (b - a) := by ring
    rw [this]
    exact dvd_sub hd_b hd_ba
  have hd_c : (d : ℤ) ∣ c := by
    have : (c : ℤ) = ↑m - b + a := by grind
    rw [this]
    exact dvd_add (dvd_sub hd_m hd_b) hd_a
  have hd_dvd_gcd : (d : ℤ) ∣ Finset.gcd {a, b, c} id :=
    Finset.dvd_gcd (fun x hx => by
      grind)
  rw [hgcd] at hd_dvd_gcd
  exact Nat.eq_one_of_dvd_one (Int.natCast_dvd_natCast.mp hd_dvd_gcd)
