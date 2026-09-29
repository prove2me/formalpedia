-- Prove2me | solution 1 for syracuse_reaches_one_below_109781
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-09T15:25:35.896982+00:00
-- url     : https://prove2.me/submissions/162ba5ab-787a-43cc-82b1-0e30d068a002

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_99781

set_option maxHeartbeats 4000000

open Nat

abbrev Reach (n : ℕ) : Prop := ∃ j : ℕ, syracuseStep^[j] n = 1

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]

theorem rs {x y : ℕ} (h : syracuseStep x = y) (hy : Reach y) : Reach x := by
  obtain ⟨j, hj⟩ := hy
  exact ⟨j + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact hj⟩

theorem stepOdd (y : ℕ) : Odd (syracuseStep y) := by
  show Odd (ordCompl[2] (3 * y + 1))
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  exact Nat.not_dvd_ordCompl Nat.prime_two (by positivity)

theorem stepPos (y : ℕ) : 0 < syracuseStep y := by
  show 0 < ordCompl[2] (3 * y + 1)
  exact Nat.ordCompl_pos 2 (by positivity)

/-- General one-step descent for `m % 4 = 1`: then `4 ∣ 3m+1`, so the odd part of
`3m+1` is at most `(3m+1)/4 < m`.  Removes every `m ≡ 1 (mod 4)` from the
explicit enumeration. -/
theorem stepLt {m : ℕ} (h1 : 1 < m) (h4 : m % 4 = 1) : syracuseStep m < m := by
  show ordCompl[2] (3 * m + 1) < m
  have hne : 3 * m + 1 ≠ 0 := by positivity
  have hdvd : 2 ^ 2 ∣ 3 * m + 1 := by omega
  have hv : 2 ≤ (3 * m + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  have hmul : 2 ^ ((3 * m + 1).factorization 2) * ordCompl[2] (3 * m + 1) = 3 * m + 1 :=
    Nat.ordProj_mul_ordCompl_eq_self (3 * m + 1) 2
  have hpow : (4 : ℕ) ≤ 2 ^ ((3 * m + 1).factorization 2) := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ ((3 * m + 1).factorization 2) := Nat.pow_le_pow_right (by norm_num) hv
  have hle4 : 4 * ordCompl[2] (3 * m + 1) ≤ 3 * m + 1 := by
    calc 4 * ordCompl[2] (3 * m + 1)
        ≤ 2 ^ ((3 * m + 1).factorization 2) * ordCompl[2] (3 * m + 1) :=
          Nat.mul_le_mul_right _ hpow
      _ = 3 * m + 1 := hmul
  omega

/-- One fused descent step with every numeral explicit: from `3y+1 = 2^a z` with
`z` odd and `Reach z`, conclude `Reach y`. -/
theorem sr (a y z : ℕ) (h : 3 * y + 1 = 2 ^ a * z) (hz : z % 2 = 1) (hy : Reach z) :
    Reach y := rs (se a h (Nat.odd_iff.mpr hz)) hy

/-- Terminal appeal to the previously verified threshold. -/
theorem B (n : ℕ) (h1 : 0 < n) (h2 : n % 2 = 1) (h3 : n < 99781) : Reach n :=
  syracuse_reaches_one_below_99781 n h1 (Nat.odd_iff.mpr h2) (by omega)

theorem R99783 : Reach 99783 := (sr 1 99783 149675 (by norm_num) (by norm_num) (sr 1 149675 224513 (by norm_num) (by norm_num) (sr 2 224513 168385 (by norm_num) (by norm_num) (sr 2 168385 126289 (by norm_num) (by norm_num) (sr 2 126289 94717 (by norm_num) (by norm_num) (B 94717 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R99787 : Reach 99787 := (sr 1 99787 149681 (by norm_num) (by norm_num) (sr 2 149681 112261 (by norm_num) (by norm_num) (sr 4 112261 21049 (by norm_num) (by norm_num) (B 21049 (by norm_num) (by norm_num) (by norm_num)))))
theorem R99791 : Reach 99791 := (sr 1 99791 149687 (by norm_num) (by norm_num) (sr 1 149687 224531 (by norm_num) (by norm_num) (sr 1 224531 336797 (by norm_num) (by norm_num) (sr 3 336797 126299 (by norm_num) (by norm_num) (sr 1 126299 189449 (by norm_num) (by norm_num) (sr 2 189449 142087 (by norm_num) (by norm_num) (sr 1 142087 213131 (by norm_num) (by norm_num) (sr 1 213131 319697 (by norm_num) (by norm_num) (sr 2 319697 239773 (by norm_num) (by norm_num) (sr 3 239773 89915 (by norm_num) (by norm_num) (B 89915 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R99795 : Reach 99795 := (sr 1 99795 149693 (by norm_num) (by norm_num) (sr 3 149693 56135 (by norm_num) (by norm_num) (B 56135 (by norm_num) (by norm_num) (by norm_num))))
theorem R99799 : Reach 99799 := (sr 1 99799 149699 (by norm_num) (by norm_num) (sr 1 149699 224549 (by norm_num) (by norm_num) (sr 4 224549 42103 (by norm_num) (by norm_num) (B 42103 (by norm_num) (by norm_num) (by norm_num)))))
theorem R99803 : Reach 99803 := (sr 1 99803 149705 (by norm_num) (by norm_num) (sr 2 149705 112279 (by norm_num) (by norm_num) (sr 1 112279 168419 (by norm_num) (by norm_num) (sr 1 168419 252629 (by norm_num) (by norm_num) (sr 7 252629 5921 (by norm_num) (by norm_num) (B 5921 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R99807 : Reach 99807 := (sr 1 99807 149711 (by norm_num) (by norm_num) (sr 1 149711 224567 (by norm_num) (by norm_num) (sr 1 224567 336851 (by norm_num) (by norm_num) (sr 1 336851 505277 (by norm_num) (by norm_num) (sr 3 505277 189479 (by norm_num) (by norm_num) (sr 1 189479 284219 (by norm_num) (by norm_num) (sr 1 284219 426329 (by norm_num) (by norm_num) (sr 2 426329 319747 (by norm_num) (by norm_num) (sr 1 319747 479621 (by norm_num) (by norm_num) (sr 4 479621 89929 (by norm_num) (by norm_num) (B 89929 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R99811 : Reach 99811 := (sr 1 99811 149717 (by norm_num) (by norm_num) (sr 7 149717 3509 (by norm_num) (by norm_num) (B 3509 (by norm_num) (by norm_num) (by norm_num))))
theorem R99815 : Reach 99815 := (sr 1 99815 149723 (by norm_num) (by norm_num) (sr 1 149723 224585 (by norm_num) (by norm_num) (sr 2 224585 168439 (by norm_num) (by norm_num) (sr 1 168439 252659 (by norm_num) (by norm_num) (sr 1 252659 378989 (by norm_num) (by norm_num) (sr 3 378989 142121 (by norm_num) (by norm_num) (sr 2 142121 106591 (by norm_num) (by norm_num) (sr 1 106591 159887 (by norm_num) (by norm_num) (sr 1 159887 239831 (by norm_num) (by norm_num) (sr 1 239831 359747 (by norm_num) (by norm_num) (sr 1 359747 539621 (by norm_num) (by norm_num) (sr 4 539621 101179 (by norm_num) (by norm_num) (sr 1 101179 151769 (by norm_num) (by norm_num) (sr 2 151769 113827 (by norm_num) (by norm_num) (sr 1 113827 170741 (by norm_num) (by norm_num) (sr 5 170741 16007 (by norm_num) (by norm_num) (B 16007 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))
theorem R99819 : Reach 99819 := (sr 1 99819 149729 (by norm_num) (by norm_num) (sr 2 149729 112297 (by norm_num) (by norm_num) (sr 2 112297 84223 (by norm_num) (by norm_num) (B 84223 (by norm_num) (by norm_num) (by norm_num)))))
theorem R99823 : Reach 99823 := (sr 1 99823 149735 (by norm_num) (by norm_num) (sr 1 149735 224603 (by norm_num) (by norm_num) (sr 1 224603 336905 (by norm_num) (by norm_num) (sr 2 336905 252679 (by norm_num) (by norm_num) (sr 1 252679 379019 (by norm_num) (by norm_num) (sr 1 379019 568529 (by norm_num) (by norm_num) (sr 2 568529 426397 (by norm_num) (by norm_num) (sr 3 426397 159899 (by norm_num) (by norm_num) (sr 1 159899 239849 (by norm_num) (by norm_num) (sr 2 239849 179887 (by norm_num) (by norm_num) (sr 1 179887 269831 (by norm_num) (by norm_num) (sr 1 269831 404747 (by norm_num) (by norm_num) (sr 1 404747 607121 (by norm_num) (by norm_num) (sr 2 607121 455341 (by norm_num) (by norm_num) (sr 3 455341 170753 (by norm_num) (by norm_num) (sr 2 170753 128065 (by norm_num) (by norm_num) (sr 2 128065 96049 (by norm_num) (by norm_num) (B 96049 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))
theorem R99827 : Reach 99827 := (sr 1 99827 149741 (by norm_num) (by norm_num) (sr 3 149741 56153 (by norm_num) (by norm_num) (B 56153 (by norm_num) (by norm_num) (by norm_num))))
theorem R99831 : Reach 99831 := (sr 1 99831 149747 (by norm_num) (by norm_num) (sr 1 149747 224621 (by norm_num) (by norm_num) (sr 3 224621 84233 (by norm_num) (by norm_num) (B 84233 (by norm_num) (by norm_num) (by norm_num)))))
theorem R99835 : Reach 99835 := (sr 1 99835 149753 (by norm_num) (by norm_num) (sr 2 149753 112315 (by norm_num) (by norm_num) (sr 1 112315 168473 (by norm_num) (by norm_num) (sr 2 168473 126355 (by norm_num) (by norm_num) (sr 1 126355 189533 (by norm_num) (by norm_num) (sr 3 189533 71075 (by norm_num) (by norm_num) (B 71075 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R99839 : Reach 99839 := (sr 1 99839 149759 (by norm_num) (by norm_num) (sr 1 149759 224639 (by norm_num) (by norm_num) (sr 1 224639 336959 (by norm_num) (by norm_num) (sr 1 336959 505439 (by norm_num) (by norm_num) (sr 1 505439 758159 (by norm_num) (by norm_num) (sr 1 758159 1137239 (by norm_num) (by norm_num) (sr 1 1137239 1705859 (by norm_num) (by norm_num) (sr 1 1705859 2558789 (by norm_num) (by norm_num) (sr 4 2558789 479773 (by norm_num) (by norm_num) (sr 3 479773 179915 (by norm_num) (by norm_num) (sr 1 179915 269873 (by norm_num) (by norm_num) (sr 2 269873 202405 (by norm_num) (by norm_num) (sr 4 202405 37951 (by norm_num) (by norm_num) (B 37951 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R99843 : Reach 99843 := (sr 1 99843 149765 (by norm_num) (by norm_num) (sr 4 149765 28081 (by norm_num) (by norm_num) (B 28081 (by norm_num) (by norm_num) (by norm_num))))
theorem R99847 : Reach 99847 := (sr 1 99847 149771 (by norm_num) (by norm_num) (sr 1 149771 224657 (by norm_num) (by norm_num) (sr 2 224657 168493 (by norm_num) (by norm_num) (sr 3 168493 63185 (by norm_num) (by norm_num) (B 63185 (by norm_num) (by norm_num) (by norm_num))))))
theorem R99851 : Reach 99851 := (sr 1 99851 149777 (by norm_num) (by norm_num) (sr 2 149777 112333 (by norm_num) (by norm_num) (sr 3 112333 42125 (by norm_num) (by norm_num) (B 42125 (by norm_num) (by norm_num) (by norm_num)))))
theorem R99855 : Reach 99855 := (sr 1 99855 149783 (by norm_num) (by norm_num) (sr 1 149783 224675 (by norm_num) (by norm_num) (sr 1 224675 337013 (by norm_num) (by norm_num) (sr 5 337013 31595 (by norm_num) (by norm_num) (B 31595 (by norm_num) (by norm_num) (by norm_num))))))
theorem R99859 : Reach 99859 := (sr 1 99859 149789 (by norm_num) (by norm_num) (sr 3 149789 56171 (by norm_num) (by norm_num) (B 56171 (by norm_num) (by norm_num) (by norm_num))))
theorem R99863 : Reach 99863 := (sr 1 99863 149795 (by norm_num) (by norm_num) (sr 1 149795 224693 (by norm_num) (by norm_num) (sr 5 224693 21065 (by norm_num) (by norm_num) (B 21065 (by norm_num) (by norm_num) (by norm_num)))))
theorem R99867 : Reach 99867 := (sr 1 99867 149801 (by norm_num) (by norm_num) (sr 2 149801 112351 (by norm_num) (by norm_num) (sr 1 112351 168527 (by norm_num) (by norm_num) (sr 1 168527 252791 (by norm_num) (by norm_num) (sr 1 252791 379187 (by norm_num) (by norm_num) (sr 1 379187 568781 (by norm_num) (by norm_num) (sr 3 568781 213293 (by norm_num) (by norm_num) (sr 3 213293 79985 (by norm_num) (by norm_num) (B 79985 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R99871 : Reach 99871 := (sr 1 99871 149807 (by norm_num) (by norm_num) (sr 1 149807 224711 (by norm_num) (by norm_num) (sr 1 224711 337067 (by norm_num) (by norm_num) (sr 1 337067 505601 (by norm_num) (by norm_num) (sr 2 505601 379201 (by norm_num) (by norm_num) (sr 2 379201 284401 (by norm_num) (by norm_num) (sr 2 284401 213301 (by norm_num) (by norm_num) (sr 5 213301 19997 (by norm_num) (by norm_num) (B 19997 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R99875 : Reach 99875 := (sr 1 99875 149813 (by norm_num) (by norm_num) (sr 5 149813 14045 (by norm_num) (by norm_num) (B 14045 (by norm_num) (by norm_num) (by norm_num))))
theorem R99879 : Reach 99879 := (sr 1 99879 149819 (by norm_num) (by norm_num) (sr 1 149819 224729 (by norm_num) (by norm_num) (sr 2 224729 168547 (by norm_num) (by norm_num) (sr 1 168547 252821 (by norm_num) (by norm_num) (sr 6 252821 11851 (by norm_num) (by norm_num) (B 11851 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R99883 : Reach 99883 := (sr 1 99883 149825 (by norm_num) (by norm_num) (sr 2 149825 112369 (by norm_num) (by norm_num) (sr 2 112369 84277 (by norm_num) (by norm_num) (B 84277 (by norm_num) (by norm_num) (by norm_num)))))
theorem R99887 : Reach 99887 := (sr 1 99887 149831 (by norm_num) (by norm_num) (sr 1 149831 224747 (by norm_num) (by norm_num) (sr 1 224747 337121 (by norm_num) (by norm_num) (sr 2 337121 252841 (by norm_num) (by norm_num) (sr 2 252841 189631 (by norm_num) (by norm_num) (sr 1 189631 284447 (by norm_num) (by norm_num) (sr 1 284447 426671 (by norm_num) (by norm_num) (sr 1 426671 640007 (by norm_num) (by norm_num) (sr 1 640007 960011 (by norm_num) (by norm_num) (sr 1 960011 1440017 (by norm_num) (by norm_num) (sr 2 1440017 1080013 (by norm_num) (by norm_num) (sr 3 1080013 405005 (by norm_num) (by norm_num) (sr 3 405005 151877 (by norm_num) (by norm_num) (sr 4 151877 28477 (by norm_num) (by norm_num) (B 28477 (by norm_num) (by norm_num) (by norm_num))))))))))))))))
theorem R99891 : Reach 99891 := (sr 1 99891 149837 (by norm_num) (by norm_num) (sr 3 149837 56189 (by norm_num) (by norm_num) (B 56189 (by norm_num) (by norm_num) (by norm_num))))
theorem R99895 : Reach 99895 := (sr 1 99895 149843 (by norm_num) (by norm_num) (sr 1 149843 224765 (by norm_num) (by norm_num) (sr 3 224765 84287 (by norm_num) (by norm_num) (B 84287 (by norm_num) (by norm_num) (by norm_num)))))
theorem R99899 : Reach 99899 := (sr 1 99899 149849 (by norm_num) (by norm_num) (sr 2 149849 112387 (by norm_num) (by norm_num) (sr 1 112387 168581 (by norm_num) (by norm_num) (sr 4 168581 31609 (by norm_num) (by norm_num) (B 31609 (by norm_num) (by norm_num) (by norm_num))))))
theorem R99903 : Reach 99903 := (sr 1 99903 149855 (by norm_num) (by norm_num) (sr 1 149855 224783 (by norm_num) (by norm_num) (sr 1 224783 337175 (by norm_num) (by norm_num) (sr 1 337175 505763 (by norm_num) (by norm_num) (sr 1 505763 758645 (by norm_num) (by norm_num) (sr 5 758645 71123 (by norm_num) (by norm_num) (B 71123 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R99907 : Reach 99907 := (sr 1 99907 149861 (by norm_num) (by norm_num) (sr 4 149861 28099 (by norm_num) (by norm_num) (B 28099 (by norm_num) (by norm_num) (by norm_num))))
theorem R99911 : Reach 99911 := (sr 1 99911 149867 (by norm_num) (by norm_num) (sr 1 149867 224801 (by norm_num) (by norm_num) (sr 2 224801 168601 (by norm_num) (by norm_num) (sr 2 168601 126451 (by norm_num) (by norm_num) (sr 1 126451 189677 (by norm_num) (by norm_num) (sr 3 189677 71129 (by norm_num) (by norm_num) (B 71129 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R99915 : Reach 99915 := (sr 1 99915 149873 (by norm_num) (by norm_num) (sr 2 149873 112405 (by norm_num) (by norm_num) (sr 6 112405 5269 (by norm_num) (by norm_num) (B 5269 (by norm_num) (by norm_num) (by norm_num)))))
theorem R99919 : Reach 99919 := (sr 1 99919 149879 (by norm_num) (by norm_num) (sr 1 149879 224819 (by norm_num) (by norm_num) (sr 1 224819 337229 (by norm_num) (by norm_num) (sr 3 337229 126461 (by norm_num) (by norm_num) (sr 3 126461 47423 (by norm_num) (by norm_num) (B 47423 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R99923 : Reach 99923 := (sr 1 99923 149885 (by norm_num) (by norm_num) (sr 3 149885 56207 (by norm_num) (by norm_num) (B 56207 (by norm_num) (by norm_num) (by norm_num))))
theorem R99927 : Reach 99927 := (sr 1 99927 149891 (by norm_num) (by norm_num) (sr 1 149891 224837 (by norm_num) (by norm_num) (sr 4 224837 42157 (by norm_num) (by norm_num) (B 42157 (by norm_num) (by norm_num) (by norm_num)))))
theorem R99931 : Reach 99931 := (sr 1 99931 149897 (by norm_num) (by norm_num) (sr 2 149897 112423 (by norm_num) (by norm_num) (sr 1 112423 168635 (by norm_num) (by norm_num) (sr 1 168635 252953 (by norm_num) (by norm_num) (sr 2 252953 189715 (by norm_num) (by norm_num) (sr 1 189715 284573 (by norm_num) (by norm_num) (sr 3 284573 106715 (by norm_num) (by norm_num) (sr 1 106715 160073 (by norm_num) (by norm_num) (sr 2 160073 120055 (by norm_num) (by norm_num) (sr 1 120055 180083 (by norm_num) (by norm_num) (sr 1 180083 270125 (by norm_num) (by norm_num) (sr 3 270125 101297 (by norm_num) (by norm_num) (sr 2 101297 75973 (by norm_num) (by norm_num) (B 75973 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R99935 : Reach 99935 := (sr 1 99935 149903 (by norm_num) (by norm_num) (sr 1 149903 224855 (by norm_num) (by norm_num) (sr 1 224855 337283 (by norm_num) (by norm_num) (sr 1 337283 505925 (by norm_num) (by norm_num) (sr 4 505925 94861 (by norm_num) (by norm_num) (B 94861 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R99939 : Reach 99939 := (sr 1 99939 149909 (by norm_num) (by norm_num) (sr 6 149909 7027 (by norm_num) (by norm_num) (B 7027 (by norm_num) (by norm_num) (by norm_num))))
theorem R99943 : Reach 99943 := (sr 1 99943 149915 (by norm_num) (by norm_num) (sr 1 149915 224873 (by norm_num) (by norm_num) (sr 2 224873 168655 (by norm_num) (by norm_num) (sr 1 168655 252983 (by norm_num) (by norm_num) (sr 1 252983 379475 (by norm_num) (by norm_num) (sr 1 379475 569213 (by norm_num) (by norm_num) (sr 3 569213 213455 (by norm_num) (by norm_num) (sr 1 213455 320183 (by norm_num) (by norm_num) (sr 1 320183 480275 (by norm_num) (by norm_num) (sr 1 480275 720413 (by norm_num) (by norm_num) (sr 3 720413 270155 (by norm_num) (by norm_num) (sr 1 270155 405233 (by norm_num) (by norm_num) (sr 2 405233 303925 (by norm_num) (by norm_num) (sr 5 303925 28493 (by norm_num) (by norm_num) (B 28493 (by norm_num) (by norm_num) (by norm_num))))))))))))))))
theorem R99947 : Reach 99947 := (sr 1 99947 149921 (by norm_num) (by norm_num) (sr 2 149921 112441 (by norm_num) (by norm_num) (sr 2 112441 84331 (by norm_num) (by norm_num) (B 84331 (by norm_num) (by norm_num) (by norm_num)))))
theorem R99951 : Reach 99951 := (sr 1 99951 149927 (by norm_num) (by norm_num) (sr 1 149927 224891 (by norm_num) (by norm_num) (sr 1 224891 337337 (by norm_num) (by norm_num) (sr 2 337337 253003 (by norm_num) (by norm_num) (sr 1 253003 379505 (by norm_num) (by norm_num) (sr 2 379505 284629 (by norm_num) (by norm_num) (sr 7 284629 6671 (by norm_num) (by norm_num) (B 6671 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R99955 : Reach 99955 := (sr 1 99955 149933 (by norm_num) (by norm_num) (sr 3 149933 56225 (by norm_num) (by norm_num) (B 56225 (by norm_num) (by norm_num) (by norm_num))))
theorem R99959 : Reach 99959 := (sr 1 99959 149939 (by norm_num) (by norm_num) (sr 1 149939 224909 (by norm_num) (by norm_num) (sr 3 224909 84341 (by norm_num) (by norm_num) (B 84341 (by norm_num) (by norm_num) (by norm_num)))))
theorem R99963 : Reach 99963 := (sr 1 99963 149945 (by norm_num) (by norm_num) (sr 2 149945 112459 (by norm_num) (by norm_num) (sr 1 112459 168689 (by norm_num) (by norm_num) (sr 2 168689 126517 (by norm_num) (by norm_num) (sr 5 126517 11861 (by norm_num) (by norm_num) (B 11861 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R99967 : Reach 99967 := (sr 1 99967 149951 (by norm_num) (by norm_num) (sr 1 149951 224927 (by norm_num) (by norm_num) (sr 1 224927 337391 (by norm_num) (by norm_num) (sr 1 337391 506087 (by norm_num) (by norm_num) (sr 1 506087 759131 (by norm_num) (by norm_num) (sr 1 759131 1138697 (by norm_num) (by norm_num) (sr 2 1138697 854023 (by norm_num) (by norm_num) (sr 1 854023 1281035 (by norm_num) (by norm_num) (sr 1 1281035 1921553 (by norm_num) (by norm_num) (sr 2 1921553 1441165 (by norm_num) (by norm_num) (sr 3 1441165 540437 (by norm_num) (by norm_num) (sr 6 540437 25333 (by norm_num) (by norm_num) (B 25333 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R99971 : Reach 99971 := (sr 1 99971 149957 (by norm_num) (by norm_num) (sr 4 149957 28117 (by norm_num) (by norm_num) (B 28117 (by norm_num) (by norm_num) (by norm_num))))
theorem R99975 : Reach 99975 := (sr 1 99975 149963 (by norm_num) (by norm_num) (sr 1 149963 224945 (by norm_num) (by norm_num) (sr 2 224945 168709 (by norm_num) (by norm_num) (sr 4 168709 31633 (by norm_num) (by norm_num) (B 31633 (by norm_num) (by norm_num) (by norm_num))))))
theorem R99979 : Reach 99979 := (sr 1 99979 149969 (by norm_num) (by norm_num) (sr 2 149969 112477 (by norm_num) (by norm_num) (sr 3 112477 42179 (by norm_num) (by norm_num) (B 42179 (by norm_num) (by norm_num) (by norm_num)))))
theorem R99983 : Reach 99983 := (sr 1 99983 149975 (by norm_num) (by norm_num) (sr 1 149975 224963 (by norm_num) (by norm_num) (sr 1 224963 337445 (by norm_num) (by norm_num) (sr 4 337445 63271 (by norm_num) (by norm_num) (B 63271 (by norm_num) (by norm_num) (by norm_num))))))
theorem R99987 : Reach 99987 := (sr 1 99987 149981 (by norm_num) (by norm_num) (sr 3 149981 56243 (by norm_num) (by norm_num) (B 56243 (by norm_num) (by norm_num) (by norm_num))))
theorem R99991 : Reach 99991 := (sr 1 99991 149987 (by norm_num) (by norm_num) (sr 1 149987 224981 (by norm_num) (by norm_num) (sr 7 224981 5273 (by norm_num) (by norm_num) (B 5273 (by norm_num) (by norm_num) (by norm_num)))))
theorem R99995 : Reach 99995 := (sr 1 99995 149993 (by norm_num) (by norm_num) (sr 2 149993 112495 (by norm_num) (by norm_num) (sr 1 112495 168743 (by norm_num) (by norm_num) (sr 1 168743 253115 (by norm_num) (by norm_num) (sr 1 253115 379673 (by norm_num) (by norm_num) (sr 2 379673 284755 (by norm_num) (by norm_num) (sr 1 284755 427133 (by norm_num) (by norm_num) (sr 3 427133 160175 (by norm_num) (by norm_num) (sr 1 160175 240263 (by norm_num) (by norm_num) (sr 1 240263 360395 (by norm_num) (by norm_num) (sr 1 360395 540593 (by norm_num) (by norm_num) (sr 2 540593 405445 (by norm_num) (by norm_num) (sr 4 405445 76021 (by norm_num) (by norm_num) (B 76021 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R99999 : Reach 99999 := (sr 1 99999 149999 (by norm_num) (by norm_num) (sr 1 149999 224999 (by norm_num) (by norm_num) (sr 1 224999 337499 (by norm_num) (by norm_num) (sr 1 337499 506249 (by norm_num) (by norm_num) (sr 2 506249 379687 (by norm_num) (by norm_num) (sr 1 379687 569531 (by norm_num) (by norm_num) (sr 1 569531 854297 (by norm_num) (by norm_num) (sr 2 854297 640723 (by norm_num) (by norm_num) (sr 1 640723 961085 (by norm_num) (by norm_num) (sr 3 961085 360407 (by norm_num) (by norm_num) (sr 1 360407 540611 (by norm_num) (by norm_num) (sr 1 540611 810917 (by norm_num) (by norm_num) (sr 4 810917 152047 (by norm_num) (by norm_num) (sr 1 152047 228071 (by norm_num) (by norm_num) (sr 1 228071 342107 (by norm_num) (by norm_num) (sr 1 342107 513161 (by norm_num) (by norm_num) (sr 2 513161 384871 (by norm_num) (by norm_num) (sr 1 384871 577307 (by norm_num) (by norm_num) (sr 1 577307 865961 (by norm_num) (by norm_num) (sr 2 865961 649471 (by norm_num) (by norm_num) (sr 1 649471 974207 (by norm_num) (by norm_num) (sr 1 974207 1461311 (by norm_num) (by norm_num) (sr 1 1461311 2191967 (by norm_num) (by norm_num) (sr 1 2191967 3287951 (by norm_num) (by norm_num) (sr 1 3287951 4931927 (by norm_num) (by norm_num) (sr 1 4931927 7397891 (by norm_num) (by norm_num) (sr 1 7397891 11096837 (by norm_num) (by norm_num) (sr 4 11096837 2080657 (by norm_num) (by norm_num) (sr 2 2080657 1560493 (by norm_num) (by norm_num) (sr 3 1560493 585185 (by norm_num) (by norm_num) (sr 2 585185 438889 (by norm_num) (by norm_num) (sr 2 438889 329167 (by norm_num) (by norm_num) (sr 1 329167 493751 (by norm_num) (by norm_num) (sr 1 493751 740627 (by norm_num) (by norm_num) (sr 1 740627 1110941 (by norm_num) (by norm_num) (sr 3 1110941 416603 (by norm_num) (by norm_num) (sr 1 416603 624905 (by norm_num) (by norm_num) (sr 2 624905 468679 (by norm_num) (by norm_num) (sr 1 468679 703019 (by norm_num) (by norm_num) (sr 1 703019 1054529 (by norm_num) (by norm_num) (sr 2 1054529 790897 (by norm_num) (by norm_num) (sr 2 790897 593173 (by norm_num) (by norm_num) (sr 6 593173 27805 (by norm_num) (by norm_num) (B 27805 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))))))))))))))))
theorem R100003 : Reach 100003 := (sr 1 100003 150005 (by norm_num) (by norm_num) (sr 5 150005 14063 (by norm_num) (by norm_num) (B 14063 (by norm_num) (by norm_num) (by norm_num))))
theorem R100007 : Reach 100007 := (sr 1 100007 150011 (by norm_num) (by norm_num) (sr 1 150011 225017 (by norm_num) (by norm_num) (sr 2 225017 168763 (by norm_num) (by norm_num) (sr 1 168763 253145 (by norm_num) (by norm_num) (sr 2 253145 189859 (by norm_num) (by norm_num) (sr 1 189859 284789 (by norm_num) (by norm_num) (sr 5 284789 26699 (by norm_num) (by norm_num) (B 26699 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R100011 : Reach 100011 := (sr 1 100011 150017 (by norm_num) (by norm_num) (sr 2 150017 112513 (by norm_num) (by norm_num) (sr 2 112513 84385 (by norm_num) (by norm_num) (B 84385 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100015 : Reach 100015 := (sr 1 100015 150023 (by norm_num) (by norm_num) (sr 1 150023 225035 (by norm_num) (by norm_num) (sr 1 225035 337553 (by norm_num) (by norm_num) (sr 2 337553 253165 (by norm_num) (by norm_num) (sr 3 253165 94937 (by norm_num) (by norm_num) (B 94937 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100019 : Reach 100019 := (sr 1 100019 150029 (by norm_num) (by norm_num) (sr 3 150029 56261 (by norm_num) (by norm_num) (B 56261 (by norm_num) (by norm_num) (by norm_num))))
theorem R100023 : Reach 100023 := (sr 1 100023 150035 (by norm_num) (by norm_num) (sr 1 150035 225053 (by norm_num) (by norm_num) (sr 3 225053 84395 (by norm_num) (by norm_num) (B 84395 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100027 : Reach 100027 := (sr 1 100027 150041 (by norm_num) (by norm_num) (sr 2 150041 112531 (by norm_num) (by norm_num) (sr 1 112531 168797 (by norm_num) (by norm_num) (sr 3 168797 63299 (by norm_num) (by norm_num) (B 63299 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100031 : Reach 100031 := (sr 1 100031 150047 (by norm_num) (by norm_num) (sr 1 150047 225071 (by norm_num) (by norm_num) (sr 1 225071 337607 (by norm_num) (by norm_num) (sr 1 337607 506411 (by norm_num) (by norm_num) (sr 1 506411 759617 (by norm_num) (by norm_num) (sr 2 759617 569713 (by norm_num) (by norm_num) (sr 2 569713 427285 (by norm_num) (by norm_num) (sr 6 427285 20029 (by norm_num) (by norm_num) (B 20029 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R100035 : Reach 100035 := (sr 1 100035 150053 (by norm_num) (by norm_num) (sr 4 150053 28135 (by norm_num) (by norm_num) (B 28135 (by norm_num) (by norm_num) (by norm_num))))
theorem R100039 : Reach 100039 := (sr 1 100039 150059 (by norm_num) (by norm_num) (sr 1 150059 225089 (by norm_num) (by norm_num) (sr 2 225089 168817 (by norm_num) (by norm_num) (sr 2 168817 126613 (by norm_num) (by norm_num) (sr 6 126613 5935 (by norm_num) (by norm_num) (B 5935 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100043 : Reach 100043 := (sr 1 100043 150065 (by norm_num) (by norm_num) (sr 2 150065 112549 (by norm_num) (by norm_num) (sr 4 112549 21103 (by norm_num) (by norm_num) (B 21103 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100047 : Reach 100047 := (sr 1 100047 150071 (by norm_num) (by norm_num) (sr 1 150071 225107 (by norm_num) (by norm_num) (sr 1 225107 337661 (by norm_num) (by norm_num) (sr 3 337661 126623 (by norm_num) (by norm_num) (sr 1 126623 189935 (by norm_num) (by norm_num) (sr 1 189935 284903 (by norm_num) (by norm_num) (sr 1 284903 427355 (by norm_num) (by norm_num) (sr 1 427355 641033 (by norm_num) (by norm_num) (sr 2 641033 480775 (by norm_num) (by norm_num) (sr 1 480775 721163 (by norm_num) (by norm_num) (sr 1 721163 1081745 (by norm_num) (by norm_num) (sr 2 1081745 811309 (by norm_num) (by norm_num) (sr 3 811309 304241 (by norm_num) (by norm_num) (sr 2 304241 228181 (by norm_num) (by norm_num) (sr 9 228181 1337 (by norm_num) (by norm_num) (B 1337 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R100051 : Reach 100051 := (sr 1 100051 150077 (by norm_num) (by norm_num) (sr 3 150077 56279 (by norm_num) (by norm_num) (B 56279 (by norm_num) (by norm_num) (by norm_num))))
theorem R100055 : Reach 100055 := (sr 1 100055 150083 (by norm_num) (by norm_num) (sr 1 150083 225125 (by norm_num) (by norm_num) (sr 4 225125 42211 (by norm_num) (by norm_num) (B 42211 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100059 : Reach 100059 := (sr 1 100059 150089 (by norm_num) (by norm_num) (sr 2 150089 112567 (by norm_num) (by norm_num) (sr 1 112567 168851 (by norm_num) (by norm_num) (sr 1 168851 253277 (by norm_num) (by norm_num) (sr 3 253277 94979 (by norm_num) (by norm_num) (B 94979 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100063 : Reach 100063 := (sr 1 100063 150095 (by norm_num) (by norm_num) (sr 1 150095 225143 (by norm_num) (by norm_num) (sr 1 225143 337715 (by norm_num) (by norm_num) (sr 1 337715 506573 (by norm_num) (by norm_num) (sr 3 506573 189965 (by norm_num) (by norm_num) (sr 3 189965 71237 (by norm_num) (by norm_num) (B 71237 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R100067 : Reach 100067 := (sr 1 100067 150101 (by norm_num) (by norm_num) (sr 8 150101 1759 (by norm_num) (by norm_num) (B 1759 (by norm_num) (by norm_num) (by norm_num))))
theorem R100071 : Reach 100071 := (sr 1 100071 150107 (by norm_num) (by norm_num) (sr 1 150107 225161 (by norm_num) (by norm_num) (sr 2 225161 168871 (by norm_num) (by norm_num) (sr 1 168871 253307 (by norm_num) (by norm_num) (sr 1 253307 379961 (by norm_num) (by norm_num) (sr 2 379961 284971 (by norm_num) (by norm_num) (sr 1 284971 427457 (by norm_num) (by norm_num) (sr 2 427457 320593 (by norm_num) (by norm_num) (sr 2 320593 240445 (by norm_num) (by norm_num) (sr 3 240445 90167 (by norm_num) (by norm_num) (B 90167 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R100075 : Reach 100075 := (sr 1 100075 150113 (by norm_num) (by norm_num) (sr 2 150113 112585 (by norm_num) (by norm_num) (sr 2 112585 84439 (by norm_num) (by norm_num) (B 84439 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100079 : Reach 100079 := (sr 1 100079 150119 (by norm_num) (by norm_num) (sr 1 150119 225179 (by norm_num) (by norm_num) (sr 1 225179 337769 (by norm_num) (by norm_num) (sr 2 337769 253327 (by norm_num) (by norm_num) (sr 1 253327 379991 (by norm_num) (by norm_num) (sr 1 379991 569987 (by norm_num) (by norm_num) (sr 1 569987 854981 (by norm_num) (by norm_num) (sr 4 854981 160309 (by norm_num) (by norm_num) (sr 5 160309 15029 (by norm_num) (by norm_num) (B 15029 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R100083 : Reach 100083 := (sr 1 100083 150125 (by norm_num) (by norm_num) (sr 3 150125 56297 (by norm_num) (by norm_num) (B 56297 (by norm_num) (by norm_num) (by norm_num))))
theorem R100087 : Reach 100087 := (sr 1 100087 150131 (by norm_num) (by norm_num) (sr 1 150131 225197 (by norm_num) (by norm_num) (sr 3 225197 84449 (by norm_num) (by norm_num) (B 84449 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100091 : Reach 100091 := (sr 1 100091 150137 (by norm_num) (by norm_num) (sr 2 150137 112603 (by norm_num) (by norm_num) (sr 1 112603 168905 (by norm_num) (by norm_num) (sr 2 168905 126679 (by norm_num) (by norm_num) (sr 1 126679 190019 (by norm_num) (by norm_num) (sr 1 190019 285029 (by norm_num) (by norm_num) (sr 4 285029 53443 (by norm_num) (by norm_num) (B 53443 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R100095 : Reach 100095 := (sr 1 100095 150143 (by norm_num) (by norm_num) (sr 1 150143 225215 (by norm_num) (by norm_num) (sr 1 225215 337823 (by norm_num) (by norm_num) (sr 1 337823 506735 (by norm_num) (by norm_num) (sr 1 506735 760103 (by norm_num) (by norm_num) (sr 1 760103 1140155 (by norm_num) (by norm_num) (sr 1 1140155 1710233 (by norm_num) (by norm_num) (sr 2 1710233 1282675 (by norm_num) (by norm_num) (sr 1 1282675 1924013 (by norm_num) (by norm_num) (sr 3 1924013 721505 (by norm_num) (by norm_num) (sr 2 721505 541129 (by norm_num) (by norm_num) (sr 2 541129 405847 (by norm_num) (by norm_num) (sr 1 405847 608771 (by norm_num) (by norm_num) (sr 1 608771 913157 (by norm_num) (by norm_num) (sr 4 913157 171217 (by norm_num) (by norm_num) (sr 2 171217 128413 (by norm_num) (by norm_num) (sr 3 128413 48155 (by norm_num) (by norm_num) (B 48155 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))
theorem R100099 : Reach 100099 := (sr 1 100099 150149 (by norm_num) (by norm_num) (sr 4 150149 28153 (by norm_num) (by norm_num) (B 28153 (by norm_num) (by norm_num) (by norm_num))))
theorem R100103 : Reach 100103 := (sr 1 100103 150155 (by norm_num) (by norm_num) (sr 1 150155 225233 (by norm_num) (by norm_num) (sr 2 225233 168925 (by norm_num) (by norm_num) (sr 3 168925 63347 (by norm_num) (by norm_num) (B 63347 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100107 : Reach 100107 := (sr 1 100107 150161 (by norm_num) (by norm_num) (sr 2 150161 112621 (by norm_num) (by norm_num) (sr 3 112621 42233 (by norm_num) (by norm_num) (B 42233 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100111 : Reach 100111 := (sr 1 100111 150167 (by norm_num) (by norm_num) (sr 1 150167 225251 (by norm_num) (by norm_num) (sr 1 225251 337877 (by norm_num) (by norm_num) (sr 7 337877 7919 (by norm_num) (by norm_num) (B 7919 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100115 : Reach 100115 := (sr 1 100115 150173 (by norm_num) (by norm_num) (sr 3 150173 56315 (by norm_num) (by norm_num) (B 56315 (by norm_num) (by norm_num) (by norm_num))))
theorem R100119 : Reach 100119 := (sr 1 100119 150179 (by norm_num) (by norm_num) (sr 1 150179 225269 (by norm_num) (by norm_num) (sr 5 225269 21119 (by norm_num) (by norm_num) (B 21119 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100123 : Reach 100123 := (sr 1 100123 150185 (by norm_num) (by norm_num) (sr 2 150185 112639 (by norm_num) (by norm_num) (sr 1 112639 168959 (by norm_num) (by norm_num) (sr 1 168959 253439 (by norm_num) (by norm_num) (sr 1 253439 380159 (by norm_num) (by norm_num) (sr 1 380159 570239 (by norm_num) (by norm_num) (sr 1 570239 855359 (by norm_num) (by norm_num) (sr 1 855359 1283039 (by norm_num) (by norm_num) (sr 1 1283039 1924559 (by norm_num) (by norm_num) (sr 1 1924559 2886839 (by norm_num) (by norm_num) (sr 1 2886839 4330259 (by norm_num) (by norm_num) (sr 1 4330259 6495389 (by norm_num) (by norm_num) (sr 3 6495389 2435771 (by norm_num) (by norm_num) (sr 1 2435771 3653657 (by norm_num) (by norm_num) (sr 2 3653657 2740243 (by norm_num) (by norm_num) (sr 1 2740243 4110365 (by norm_num) (by norm_num) (sr 3 4110365 1541387 (by norm_num) (by norm_num) (sr 1 1541387 2312081 (by norm_num) (by norm_num) (sr 2 2312081 1734061 (by norm_num) (by norm_num) (sr 3 1734061 650273 (by norm_num) (by norm_num) (sr 2 650273 487705 (by norm_num) (by norm_num) (sr 2 487705 365779 (by norm_num) (by norm_num) (sr 1 365779 548669 (by norm_num) (by norm_num) (sr 3 548669 205751 (by norm_num) (by norm_num) (sr 1 205751 308627 (by norm_num) (by norm_num) (sr 1 308627 462941 (by norm_num) (by norm_num) (sr 3 462941 173603 (by norm_num) (by norm_num) (sr 1 173603 260405 (by norm_num) (by norm_num) (sr 5 260405 24413 (by norm_num) (by norm_num) (B 24413 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))
theorem R100127 : Reach 100127 := (sr 1 100127 150191 (by norm_num) (by norm_num) (sr 1 150191 225287 (by norm_num) (by norm_num) (sr 1 225287 337931 (by norm_num) (by norm_num) (sr 1 337931 506897 (by norm_num) (by norm_num) (sr 2 506897 380173 (by norm_num) (by norm_num) (sr 3 380173 142565 (by norm_num) (by norm_num) (sr 4 142565 26731 (by norm_num) (by norm_num) (B 26731 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R100131 : Reach 100131 := (sr 1 100131 150197 (by norm_num) (by norm_num) (sr 5 150197 14081 (by norm_num) (by norm_num) (B 14081 (by norm_num) (by norm_num) (by norm_num))))
theorem R100135 : Reach 100135 := (sr 1 100135 150203 (by norm_num) (by norm_num) (sr 1 150203 225305 (by norm_num) (by norm_num) (sr 2 225305 168979 (by norm_num) (by norm_num) (sr 1 168979 253469 (by norm_num) (by norm_num) (sr 3 253469 95051 (by norm_num) (by norm_num) (B 95051 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100139 : Reach 100139 := (sr 1 100139 150209 (by norm_num) (by norm_num) (sr 2 150209 112657 (by norm_num) (by norm_num) (sr 2 112657 84493 (by norm_num) (by norm_num) (B 84493 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100143 : Reach 100143 := (sr 1 100143 150215 (by norm_num) (by norm_num) (sr 1 150215 225323 (by norm_num) (by norm_num) (sr 1 225323 337985 (by norm_num) (by norm_num) (sr 2 337985 253489 (by norm_num) (by norm_num) (sr 2 253489 190117 (by norm_num) (by norm_num) (sr 4 190117 35647 (by norm_num) (by norm_num) (B 35647 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R100147 : Reach 100147 := (sr 1 100147 150221 (by norm_num) (by norm_num) (sr 3 150221 56333 (by norm_num) (by norm_num) (B 56333 (by norm_num) (by norm_num) (by norm_num))))
theorem R100151 : Reach 100151 := (sr 1 100151 150227 (by norm_num) (by norm_num) (sr 1 150227 225341 (by norm_num) (by norm_num) (sr 3 225341 84503 (by norm_num) (by norm_num) (B 84503 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100155 : Reach 100155 := (sr 1 100155 150233 (by norm_num) (by norm_num) (sr 2 150233 112675 (by norm_num) (by norm_num) (sr 1 112675 169013 (by norm_num) (by norm_num) (sr 5 169013 15845 (by norm_num) (by norm_num) (B 15845 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100159 : Reach 100159 := (sr 1 100159 150239 (by norm_num) (by norm_num) (sr 1 150239 225359 (by norm_num) (by norm_num) (sr 1 225359 338039 (by norm_num) (by norm_num) (sr 1 338039 507059 (by norm_num) (by norm_num) (sr 1 507059 760589 (by norm_num) (by norm_num) (sr 3 760589 285221 (by norm_num) (by norm_num) (sr 4 285221 53479 (by norm_num) (by norm_num) (B 53479 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R100163 : Reach 100163 := (sr 1 100163 150245 (by norm_num) (by norm_num) (sr 4 150245 28171 (by norm_num) (by norm_num) (B 28171 (by norm_num) (by norm_num) (by norm_num))))
theorem R100167 : Reach 100167 := (sr 1 100167 150251 (by norm_num) (by norm_num) (sr 1 150251 225377 (by norm_num) (by norm_num) (sr 2 225377 169033 (by norm_num) (by norm_num) (sr 2 169033 126775 (by norm_num) (by norm_num) (sr 1 126775 190163 (by norm_num) (by norm_num) (sr 1 190163 285245 (by norm_num) (by norm_num) (sr 3 285245 106967 (by norm_num) (by norm_num) (sr 1 106967 160451 (by norm_num) (by norm_num) (sr 1 160451 240677 (by norm_num) (by norm_num) (sr 4 240677 45127 (by norm_num) (by norm_num) (B 45127 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R100171 : Reach 100171 := (sr 1 100171 150257 (by norm_num) (by norm_num) (sr 2 150257 112693 (by norm_num) (by norm_num) (sr 5 112693 10565 (by norm_num) (by norm_num) (B 10565 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100175 : Reach 100175 := (sr 1 100175 150263 (by norm_num) (by norm_num) (sr 1 150263 225395 (by norm_num) (by norm_num) (sr 1 225395 338093 (by norm_num) (by norm_num) (sr 3 338093 126785 (by norm_num) (by norm_num) (sr 2 126785 95089 (by norm_num) (by norm_num) (B 95089 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100179 : Reach 100179 := (sr 1 100179 150269 (by norm_num) (by norm_num) (sr 3 150269 56351 (by norm_num) (by norm_num) (B 56351 (by norm_num) (by norm_num) (by norm_num))))
theorem R100183 : Reach 100183 := (sr 1 100183 150275 (by norm_num) (by norm_num) (sr 1 150275 225413 (by norm_num) (by norm_num) (sr 4 225413 42265 (by norm_num) (by norm_num) (B 42265 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100187 : Reach 100187 := (sr 1 100187 150281 (by norm_num) (by norm_num) (sr 2 150281 112711 (by norm_num) (by norm_num) (sr 1 112711 169067 (by norm_num) (by norm_num) (sr 1 169067 253601 (by norm_num) (by norm_num) (sr 2 253601 190201 (by norm_num) (by norm_num) (sr 2 190201 142651 (by norm_num) (by norm_num) (sr 1 142651 213977 (by norm_num) (by norm_num) (sr 2 213977 160483 (by norm_num) (by norm_num) (sr 1 160483 240725 (by norm_num) (by norm_num) (sr 8 240725 2821 (by norm_num) (by norm_num) (B 2821 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R100191 : Reach 100191 := (sr 1 100191 150287 (by norm_num) (by norm_num) (sr 1 150287 225431 (by norm_num) (by norm_num) (sr 1 225431 338147 (by norm_num) (by norm_num) (sr 1 338147 507221 (by norm_num) (by norm_num) (sr 11 507221 743 (by norm_num) (by norm_num) (B 743 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100195 : Reach 100195 := (sr 1 100195 150293 (by norm_num) (by norm_num) (sr 6 150293 7045 (by norm_num) (by norm_num) (B 7045 (by norm_num) (by norm_num) (by norm_num))))
theorem R100199 : Reach 100199 := (sr 1 100199 150299 (by norm_num) (by norm_num) (sr 1 150299 225449 (by norm_num) (by norm_num) (sr 2 225449 169087 (by norm_num) (by norm_num) (sr 1 169087 253631 (by norm_num) (by norm_num) (sr 1 253631 380447 (by norm_num) (by norm_num) (sr 1 380447 570671 (by norm_num) (by norm_num) (sr 1 570671 856007 (by norm_num) (by norm_num) (sr 1 856007 1284011 (by norm_num) (by norm_num) (sr 1 1284011 1926017 (by norm_num) (by norm_num) (sr 2 1926017 1444513 (by norm_num) (by norm_num) (sr 2 1444513 1083385 (by norm_num) (by norm_num) (sr 2 1083385 812539 (by norm_num) (by norm_num) (sr 1 812539 1218809 (by norm_num) (by norm_num) (sr 2 1218809 914107 (by norm_num) (by norm_num) (sr 1 914107 1371161 (by norm_num) (by norm_num) (sr 2 1371161 1028371 (by norm_num) (by norm_num) (sr 1 1028371 1542557 (by norm_num) (by norm_num) (sr 3 1542557 578459 (by norm_num) (by norm_num) (sr 1 578459 867689 (by norm_num) (by norm_num) (sr 2 867689 650767 (by norm_num) (by norm_num) (sr 1 650767 976151 (by norm_num) (by norm_num) (sr 1 976151 1464227 (by norm_num) (by norm_num) (sr 1 1464227 2196341 (by norm_num) (by norm_num) (sr 5 2196341 205907 (by norm_num) (by norm_num) (sr 1 205907 308861 (by norm_num) (by norm_num) (sr 3 308861 115823 (by norm_num) (by norm_num) (sr 1 115823 173735 (by norm_num) (by norm_num) (sr 1 173735 260603 (by norm_num) (by norm_num) (sr 1 260603 390905 (by norm_num) (by norm_num) (sr 2 390905 293179 (by norm_num) (by norm_num) (sr 1 293179 439769 (by norm_num) (by norm_num) (sr 2 439769 329827 (by norm_num) (by norm_num) (sr 1 329827 494741 (by norm_num) (by norm_num) (sr 6 494741 23191 (by norm_num) (by norm_num) (B 23191 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))))))))
theorem R100203 : Reach 100203 := (sr 1 100203 150305 (by norm_num) (by norm_num) (sr 2 150305 112729 (by norm_num) (by norm_num) (sr 2 112729 84547 (by norm_num) (by norm_num) (B 84547 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100207 : Reach 100207 := (sr 1 100207 150311 (by norm_num) (by norm_num) (sr 1 150311 225467 (by norm_num) (by norm_num) (sr 1 225467 338201 (by norm_num) (by norm_num) (sr 2 338201 253651 (by norm_num) (by norm_num) (sr 1 253651 380477 (by norm_num) (by norm_num) (sr 3 380477 142679 (by norm_num) (by norm_num) (sr 1 142679 214019 (by norm_num) (by norm_num) (sr 1 214019 321029 (by norm_num) (by norm_num) (sr 4 321029 60193 (by norm_num) (by norm_num) (B 60193 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R100211 : Reach 100211 := (sr 1 100211 150317 (by norm_num) (by norm_num) (sr 3 150317 56369 (by norm_num) (by norm_num) (B 56369 (by norm_num) (by norm_num) (by norm_num))))
theorem R100215 : Reach 100215 := (sr 1 100215 150323 (by norm_num) (by norm_num) (sr 1 150323 225485 (by norm_num) (by norm_num) (sr 3 225485 84557 (by norm_num) (by norm_num) (B 84557 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100219 : Reach 100219 := (sr 1 100219 150329 (by norm_num) (by norm_num) (sr 2 150329 112747 (by norm_num) (by norm_num) (sr 1 112747 169121 (by norm_num) (by norm_num) (sr 2 169121 126841 (by norm_num) (by norm_num) (sr 2 126841 95131 (by norm_num) (by norm_num) (B 95131 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100223 : Reach 100223 := (sr 1 100223 150335 (by norm_num) (by norm_num) (sr 1 150335 225503 (by norm_num) (by norm_num) (sr 1 225503 338255 (by norm_num) (by norm_num) (sr 1 338255 507383 (by norm_num) (by norm_num) (sr 1 507383 761075 (by norm_num) (by norm_num) (sr 1 761075 1141613 (by norm_num) (by norm_num) (sr 3 1141613 428105 (by norm_num) (by norm_num) (sr 2 428105 321079 (by norm_num) (by norm_num) (sr 1 321079 481619 (by norm_num) (by norm_num) (sr 1 481619 722429 (by norm_num) (by norm_num) (sr 3 722429 270911 (by norm_num) (by norm_num) (sr 1 270911 406367 (by norm_num) (by norm_num) (sr 1 406367 609551 (by norm_num) (by norm_num) (sr 1 609551 914327 (by norm_num) (by norm_num) (sr 1 914327 1371491 (by norm_num) (by norm_num) (sr 1 1371491 2057237 (by norm_num) (by norm_num) (sr 6 2057237 96433 (by norm_num) (by norm_num) (B 96433 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))
theorem R100227 : Reach 100227 := (sr 1 100227 150341 (by norm_num) (by norm_num) (sr 4 150341 28189 (by norm_num) (by norm_num) (B 28189 (by norm_num) (by norm_num) (by norm_num))))
theorem R100231 : Reach 100231 := (sr 1 100231 150347 (by norm_num) (by norm_num) (sr 1 150347 225521 (by norm_num) (by norm_num) (sr 2 225521 169141 (by norm_num) (by norm_num) (sr 5 169141 15857 (by norm_num) (by norm_num) (B 15857 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100235 : Reach 100235 := (sr 1 100235 150353 (by norm_num) (by norm_num) (sr 2 150353 112765 (by norm_num) (by norm_num) (sr 3 112765 42287 (by norm_num) (by norm_num) (B 42287 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100239 : Reach 100239 := (sr 1 100239 150359 (by norm_num) (by norm_num) (sr 1 150359 225539 (by norm_num) (by norm_num) (sr 1 225539 338309 (by norm_num) (by norm_num) (sr 4 338309 63433 (by norm_num) (by norm_num) (B 63433 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100243 : Reach 100243 := (sr 1 100243 150365 (by norm_num) (by norm_num) (sr 3 150365 56387 (by norm_num) (by norm_num) (B 56387 (by norm_num) (by norm_num) (by norm_num))))
theorem R100247 : Reach 100247 := (sr 1 100247 150371 (by norm_num) (by norm_num) (sr 1 150371 225557 (by norm_num) (by norm_num) (sr 6 225557 10573 (by norm_num) (by norm_num) (B 10573 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100251 : Reach 100251 := (sr 1 100251 150377 (by norm_num) (by norm_num) (sr 2 150377 112783 (by norm_num) (by norm_num) (sr 1 112783 169175 (by norm_num) (by norm_num) (sr 1 169175 253763 (by norm_num) (by norm_num) (sr 1 253763 380645 (by norm_num) (by norm_num) (sr 4 380645 71371 (by norm_num) (by norm_num) (B 71371 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R100255 : Reach 100255 := (sr 1 100255 150383 (by norm_num) (by norm_num) (sr 1 150383 225575 (by norm_num) (by norm_num) (sr 1 225575 338363 (by norm_num) (by norm_num) (sr 1 338363 507545 (by norm_num) (by norm_num) (sr 2 507545 380659 (by norm_num) (by norm_num) (sr 1 380659 570989 (by norm_num) (by norm_num) (sr 3 570989 214121 (by norm_num) (by norm_num) (sr 2 214121 160591 (by norm_num) (by norm_num) (sr 1 160591 240887 (by norm_num) (by norm_num) (sr 1 240887 361331 (by norm_num) (by norm_num) (sr 1 361331 541997 (by norm_num) (by norm_num) (sr 3 541997 203249 (by norm_num) (by norm_num) (sr 2 203249 152437 (by norm_num) (by norm_num) (sr 5 152437 14291 (by norm_num) (by norm_num) (B 14291 (by norm_num) (by norm_num) (by norm_num))))))))))))))))
theorem R100259 : Reach 100259 := (sr 1 100259 150389 (by norm_num) (by norm_num) (sr 5 150389 14099 (by norm_num) (by norm_num) (B 14099 (by norm_num) (by norm_num) (by norm_num))))
theorem R100263 : Reach 100263 := (sr 1 100263 150395 (by norm_num) (by norm_num) (sr 1 150395 225593 (by norm_num) (by norm_num) (sr 2 225593 169195 (by norm_num) (by norm_num) (sr 1 169195 253793 (by norm_num) (by norm_num) (sr 2 253793 190345 (by norm_num) (by norm_num) (sr 2 190345 142759 (by norm_num) (by norm_num) (sr 1 142759 214139 (by norm_num) (by norm_num) (sr 1 214139 321209 (by norm_num) (by norm_num) (sr 2 321209 240907 (by norm_num) (by norm_num) (sr 1 240907 361361 (by norm_num) (by norm_num) (sr 2 361361 271021 (by norm_num) (by norm_num) (sr 3 271021 101633 (by norm_num) (by norm_num) (sr 2 101633 76225 (by norm_num) (by norm_num) (B 76225 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R100267 : Reach 100267 := (sr 1 100267 150401 (by norm_num) (by norm_num) (sr 2 150401 112801 (by norm_num) (by norm_num) (sr 2 112801 84601 (by norm_num) (by norm_num) (B 84601 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100271 : Reach 100271 := (sr 1 100271 150407 (by norm_num) (by norm_num) (sr 1 150407 225611 (by norm_num) (by norm_num) (sr 1 225611 338417 (by norm_num) (by norm_num) (sr 2 338417 253813 (by norm_num) (by norm_num) (sr 5 253813 23795 (by norm_num) (by norm_num) (B 23795 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100275 : Reach 100275 := (sr 1 100275 150413 (by norm_num) (by norm_num) (sr 3 150413 56405 (by norm_num) (by norm_num) (B 56405 (by norm_num) (by norm_num) (by norm_num))))
theorem R100279 : Reach 100279 := (sr 1 100279 150419 (by norm_num) (by norm_num) (sr 1 150419 225629 (by norm_num) (by norm_num) (sr 3 225629 84611 (by norm_num) (by norm_num) (B 84611 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100283 : Reach 100283 := (sr 1 100283 150425 (by norm_num) (by norm_num) (sr 2 150425 112819 (by norm_num) (by norm_num) (sr 1 112819 169229 (by norm_num) (by norm_num) (sr 3 169229 63461 (by norm_num) (by norm_num) (B 63461 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100287 : Reach 100287 := (sr 1 100287 150431 (by norm_num) (by norm_num) (sr 1 150431 225647 (by norm_num) (by norm_num) (sr 1 225647 338471 (by norm_num) (by norm_num) (sr 1 338471 507707 (by norm_num) (by norm_num) (sr 1 507707 761561 (by norm_num) (by norm_num) (sr 2 761561 571171 (by norm_num) (by norm_num) (sr 1 571171 856757 (by norm_num) (by norm_num) (sr 5 856757 80321 (by norm_num) (by norm_num) (B 80321 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R100291 : Reach 100291 := (sr 1 100291 150437 (by norm_num) (by norm_num) (sr 4 150437 28207 (by norm_num) (by norm_num) (B 28207 (by norm_num) (by norm_num) (by norm_num))))
theorem R100295 : Reach 100295 := (sr 1 100295 150443 (by norm_num) (by norm_num) (sr 1 150443 225665 (by norm_num) (by norm_num) (sr 2 225665 169249 (by norm_num) (by norm_num) (sr 2 169249 126937 (by norm_num) (by norm_num) (sr 2 126937 95203 (by norm_num) (by norm_num) (B 95203 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100299 : Reach 100299 := (sr 1 100299 150449 (by norm_num) (by norm_num) (sr 2 150449 112837 (by norm_num) (by norm_num) (sr 4 112837 21157 (by norm_num) (by norm_num) (B 21157 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100303 : Reach 100303 := (sr 1 100303 150455 (by norm_num) (by norm_num) (sr 1 150455 225683 (by norm_num) (by norm_num) (sr 1 225683 338525 (by norm_num) (by norm_num) (sr 3 338525 126947 (by norm_num) (by norm_num) (sr 1 126947 190421 (by norm_num) (by norm_num) (sr 7 190421 4463 (by norm_num) (by norm_num) (B 4463 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R100307 : Reach 100307 := (sr 1 100307 150461 (by norm_num) (by norm_num) (sr 3 150461 56423 (by norm_num) (by norm_num) (B 56423 (by norm_num) (by norm_num) (by norm_num))))
theorem R100311 : Reach 100311 := (sr 1 100311 150467 (by norm_num) (by norm_num) (sr 1 150467 225701 (by norm_num) (by norm_num) (sr 4 225701 42319 (by norm_num) (by norm_num) (B 42319 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100315 : Reach 100315 := (sr 1 100315 150473 (by norm_num) (by norm_num) (sr 2 150473 112855 (by norm_num) (by norm_num) (sr 1 112855 169283 (by norm_num) (by norm_num) (sr 1 169283 253925 (by norm_num) (by norm_num) (sr 4 253925 47611 (by norm_num) (by norm_num) (B 47611 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100319 : Reach 100319 := (sr 1 100319 150479 (by norm_num) (by norm_num) (sr 1 150479 225719 (by norm_num) (by norm_num) (sr 1 225719 338579 (by norm_num) (by norm_num) (sr 1 338579 507869 (by norm_num) (by norm_num) (sr 3 507869 190451 (by norm_num) (by norm_num) (sr 1 190451 285677 (by norm_num) (by norm_num) (sr 3 285677 107129 (by norm_num) (by norm_num) (sr 2 107129 80347 (by norm_num) (by norm_num) (B 80347 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R100323 : Reach 100323 := (sr 1 100323 150485 (by norm_num) (by norm_num) (sr 7 150485 3527 (by norm_num) (by norm_num) (B 3527 (by norm_num) (by norm_num) (by norm_num))))
theorem R100327 : Reach 100327 := (sr 1 100327 150491 (by norm_num) (by norm_num) (sr 1 150491 225737 (by norm_num) (by norm_num) (sr 2 225737 169303 (by norm_num) (by norm_num) (sr 1 169303 253955 (by norm_num) (by norm_num) (sr 1 253955 380933 (by norm_num) (by norm_num) (sr 4 380933 71425 (by norm_num) (by norm_num) (B 71425 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R100331 : Reach 100331 := (sr 1 100331 150497 (by norm_num) (by norm_num) (sr 2 150497 112873 (by norm_num) (by norm_num) (sr 2 112873 84655 (by norm_num) (by norm_num) (B 84655 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100335 : Reach 100335 := (sr 1 100335 150503 (by norm_num) (by norm_num) (sr 1 150503 225755 (by norm_num) (by norm_num) (sr 1 225755 338633 (by norm_num) (by norm_num) (sr 2 338633 253975 (by norm_num) (by norm_num) (sr 1 253975 380963 (by norm_num) (by norm_num) (sr 1 380963 571445 (by norm_num) (by norm_num) (sr 5 571445 53573 (by norm_num) (by norm_num) (B 53573 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R100339 : Reach 100339 := (sr 1 100339 150509 (by norm_num) (by norm_num) (sr 3 150509 56441 (by norm_num) (by norm_num) (B 56441 (by norm_num) (by norm_num) (by norm_num))))
theorem R100343 : Reach 100343 := (sr 1 100343 150515 (by norm_num) (by norm_num) (sr 1 150515 225773 (by norm_num) (by norm_num) (sr 3 225773 84665 (by norm_num) (by norm_num) (B 84665 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100347 : Reach 100347 := (sr 1 100347 150521 (by norm_num) (by norm_num) (sr 2 150521 112891 (by norm_num) (by norm_num) (sr 1 112891 169337 (by norm_num) (by norm_num) (sr 2 169337 127003 (by norm_num) (by norm_num) (sr 1 127003 190505 (by norm_num) (by norm_num) (sr 2 190505 142879 (by norm_num) (by norm_num) (sr 1 142879 214319 (by norm_num) (by norm_num) (sr 1 214319 321479 (by norm_num) (by norm_num) (sr 1 321479 482219 (by norm_num) (by norm_num) (sr 1 482219 723329 (by norm_num) (by norm_num) (sr 2 723329 542497 (by norm_num) (by norm_num) (sr 2 542497 406873 (by norm_num) (by norm_num) (sr 2 406873 305155 (by norm_num) (by norm_num) (sr 1 305155 457733 (by norm_num) (by norm_num) (sr 4 457733 85825 (by norm_num) (by norm_num) (B 85825 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R100351 : Reach 100351 := (sr 1 100351 150527 (by norm_num) (by norm_num) (sr 1 150527 225791 (by norm_num) (by norm_num) (sr 1 225791 338687 (by norm_num) (by norm_num) (sr 1 338687 508031 (by norm_num) (by norm_num) (sr 1 508031 762047 (by norm_num) (by norm_num) (sr 1 762047 1143071 (by norm_num) (by norm_num) (sr 1 1143071 1714607 (by norm_num) (by norm_num) (sr 1 1714607 2571911 (by norm_num) (by norm_num) (sr 1 2571911 3857867 (by norm_num) (by norm_num) (sr 1 3857867 5786801 (by norm_num) (by norm_num) (sr 2 5786801 4340101 (by norm_num) (by norm_num) (sr 4 4340101 813769 (by norm_num) (by norm_num) (sr 2 813769 610327 (by norm_num) (by norm_num) (sr 1 610327 915491 (by norm_num) (by norm_num) (sr 1 915491 1373237 (by norm_num) (by norm_num) (sr 5 1373237 128741 (by norm_num) (by norm_num) (sr 4 128741 24139 (by norm_num) (by norm_num) (B 24139 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))
theorem R100355 : Reach 100355 := (sr 1 100355 150533 (by norm_num) (by norm_num) (sr 4 150533 28225 (by norm_num) (by norm_num) (B 28225 (by norm_num) (by norm_num) (by norm_num))))
theorem R100359 : Reach 100359 := (sr 1 100359 150539 (by norm_num) (by norm_num) (sr 1 150539 225809 (by norm_num) (by norm_num) (sr 2 225809 169357 (by norm_num) (by norm_num) (sr 3 169357 63509 (by norm_num) (by norm_num) (B 63509 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100363 : Reach 100363 := (sr 1 100363 150545 (by norm_num) (by norm_num) (sr 2 150545 112909 (by norm_num) (by norm_num) (sr 3 112909 42341 (by norm_num) (by norm_num) (B 42341 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100367 : Reach 100367 := (sr 1 100367 150551 (by norm_num) (by norm_num) (sr 1 150551 225827 (by norm_num) (by norm_num) (sr 1 225827 338741 (by norm_num) (by norm_num) (sr 5 338741 31757 (by norm_num) (by norm_num) (B 31757 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100371 : Reach 100371 := (sr 1 100371 150557 (by norm_num) (by norm_num) (sr 3 150557 56459 (by norm_num) (by norm_num) (B 56459 (by norm_num) (by norm_num) (by norm_num))))
theorem R100375 : Reach 100375 := (sr 1 100375 150563 (by norm_num) (by norm_num) (sr 1 150563 225845 (by norm_num) (by norm_num) (sr 5 225845 21173 (by norm_num) (by norm_num) (B 21173 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100379 : Reach 100379 := (sr 1 100379 150569 (by norm_num) (by norm_num) (sr 2 150569 112927 (by norm_num) (by norm_num) (sr 1 112927 169391 (by norm_num) (by norm_num) (sr 1 169391 254087 (by norm_num) (by norm_num) (sr 1 254087 381131 (by norm_num) (by norm_num) (sr 1 381131 571697 (by norm_num) (by norm_num) (sr 2 571697 428773 (by norm_num) (by norm_num) (sr 4 428773 80395 (by norm_num) (by norm_num) (B 80395 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R100383 : Reach 100383 := (sr 1 100383 150575 (by norm_num) (by norm_num) (sr 1 150575 225863 (by norm_num) (by norm_num) (sr 1 225863 338795 (by norm_num) (by norm_num) (sr 1 338795 508193 (by norm_num) (by norm_num) (sr 2 508193 381145 (by norm_num) (by norm_num) (sr 2 381145 285859 (by norm_num) (by norm_num) (sr 1 285859 428789 (by norm_num) (by norm_num) (sr 5 428789 40199 (by norm_num) (by norm_num) (B 40199 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R100387 : Reach 100387 := (sr 1 100387 150581 (by norm_num) (by norm_num) (sr 5 150581 14117 (by norm_num) (by norm_num) (B 14117 (by norm_num) (by norm_num) (by norm_num))))
theorem R100391 : Reach 100391 := (sr 1 100391 150587 (by norm_num) (by norm_num) (sr 1 150587 225881 (by norm_num) (by norm_num) (sr 2 225881 169411 (by norm_num) (by norm_num) (sr 1 169411 254117 (by norm_num) (by norm_num) (sr 4 254117 47647 (by norm_num) (by norm_num) (B 47647 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100395 : Reach 100395 := (sr 1 100395 150593 (by norm_num) (by norm_num) (sr 2 150593 112945 (by norm_num) (by norm_num) (sr 2 112945 84709 (by norm_num) (by norm_num) (B 84709 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100399 : Reach 100399 := (sr 1 100399 150599 (by norm_num) (by norm_num) (sr 1 150599 225899 (by norm_num) (by norm_num) (sr 1 225899 338849 (by norm_num) (by norm_num) (sr 2 338849 254137 (by norm_num) (by norm_num) (sr 2 254137 190603 (by norm_num) (by norm_num) (sr 1 190603 285905 (by norm_num) (by norm_num) (sr 2 285905 214429 (by norm_num) (by norm_num) (sr 3 214429 80411 (by norm_num) (by norm_num) (B 80411 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R100403 : Reach 100403 := (sr 1 100403 150605 (by norm_num) (by norm_num) (sr 3 150605 56477 (by norm_num) (by norm_num) (B 56477 (by norm_num) (by norm_num) (by norm_num))))
theorem R100407 : Reach 100407 := (sr 1 100407 150611 (by norm_num) (by norm_num) (sr 1 150611 225917 (by norm_num) (by norm_num) (sr 3 225917 84719 (by norm_num) (by norm_num) (B 84719 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100411 : Reach 100411 := (sr 1 100411 150617 (by norm_num) (by norm_num) (sr 2 150617 112963 (by norm_num) (by norm_num) (sr 1 112963 169445 (by norm_num) (by norm_num) (sr 4 169445 31771 (by norm_num) (by norm_num) (B 31771 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100415 : Reach 100415 := (sr 1 100415 150623 (by norm_num) (by norm_num) (sr 1 150623 225935 (by norm_num) (by norm_num) (sr 1 225935 338903 (by norm_num) (by norm_num) (sr 1 338903 508355 (by norm_num) (by norm_num) (sr 1 508355 762533 (by norm_num) (by norm_num) (sr 4 762533 142975 (by norm_num) (by norm_num) (sr 1 142975 214463 (by norm_num) (by norm_num) (sr 1 214463 321695 (by norm_num) (by norm_num) (sr 1 321695 482543 (by norm_num) (by norm_num) (sr 1 482543 723815 (by norm_num) (by norm_num) (sr 1 723815 1085723 (by norm_num) (by norm_num) (sr 1 1085723 1628585 (by norm_num) (by norm_num) (sr 2 1628585 1221439 (by norm_num) (by norm_num) (sr 1 1221439 1832159 (by norm_num) (by norm_num) (sr 1 1832159 2748239 (by norm_num) (by norm_num) (sr 1 2748239 4122359 (by norm_num) (by norm_num) (sr 1 4122359 6183539 (by norm_num) (by norm_num) (sr 1 6183539 9275309 (by norm_num) (by norm_num) (sr 3 9275309 3478241 (by norm_num) (by norm_num) (sr 2 3478241 2608681 (by norm_num) (by norm_num) (sr 2 2608681 1956511 (by norm_num) (by norm_num) (sr 1 1956511 2934767 (by norm_num) (by norm_num) (sr 1 2934767 4402151 (by norm_num) (by norm_num) (sr 1 4402151 6603227 (by norm_num) (by norm_num) (sr 1 6603227 9904841 (by norm_num) (by norm_num) (sr 2 9904841 7428631 (by norm_num) (by norm_num) (sr 1 7428631 11142947 (by norm_num) (by norm_num) (sr 1 11142947 16714421 (by norm_num) (by norm_num) (sr 5 16714421 1566977 (by norm_num) (by norm_num) (sr 2 1566977 1175233 (by norm_num) (by norm_num) (sr 2 1175233 881425 (by norm_num) (by norm_num) (sr 2 881425 661069 (by norm_num) (by norm_num) (sr 3 661069 247901 (by norm_num) (by norm_num) (sr 3 247901 92963 (by norm_num) (by norm_num) (B 92963 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))))))))
theorem R100419 : Reach 100419 := (sr 1 100419 150629 (by norm_num) (by norm_num) (sr 4 150629 28243 (by norm_num) (by norm_num) (B 28243 (by norm_num) (by norm_num) (by norm_num))))
theorem R100423 : Reach 100423 := (sr 1 100423 150635 (by norm_num) (by norm_num) (sr 1 150635 225953 (by norm_num) (by norm_num) (sr 2 225953 169465 (by norm_num) (by norm_num) (sr 2 169465 127099 (by norm_num) (by norm_num) (sr 1 127099 190649 (by norm_num) (by norm_num) (sr 2 190649 142987 (by norm_num) (by norm_num) (sr 1 142987 214481 (by norm_num) (by norm_num) (sr 2 214481 160861 (by norm_num) (by norm_num) (sr 3 160861 60323 (by norm_num) (by norm_num) (B 60323 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R100427 : Reach 100427 := (sr 1 100427 150641 (by norm_num) (by norm_num) (sr 2 150641 112981 (by norm_num) (by norm_num) (sr 10 112981 331 (by norm_num) (by norm_num) (B 331 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100431 : Reach 100431 := (sr 1 100431 150647 (by norm_num) (by norm_num) (sr 1 150647 225971 (by norm_num) (by norm_num) (sr 1 225971 338957 (by norm_num) (by norm_num) (sr 3 338957 127109 (by norm_num) (by norm_num) (sr 4 127109 23833 (by norm_num) (by norm_num) (B 23833 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100435 : Reach 100435 := (sr 1 100435 150653 (by norm_num) (by norm_num) (sr 3 150653 56495 (by norm_num) (by norm_num) (B 56495 (by norm_num) (by norm_num) (by norm_num))))
theorem R100439 : Reach 100439 := (sr 1 100439 150659 (by norm_num) (by norm_num) (sr 1 150659 225989 (by norm_num) (by norm_num) (sr 4 225989 42373 (by norm_num) (by norm_num) (B 42373 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100443 : Reach 100443 := (sr 1 100443 150665 (by norm_num) (by norm_num) (sr 2 150665 112999 (by norm_num) (by norm_num) (sr 1 112999 169499 (by norm_num) (by norm_num) (sr 1 169499 254249 (by norm_num) (by norm_num) (sr 2 254249 190687 (by norm_num) (by norm_num) (sr 1 190687 286031 (by norm_num) (by norm_num) (sr 1 286031 429047 (by norm_num) (by norm_num) (sr 1 429047 643571 (by norm_num) (by norm_num) (sr 1 643571 965357 (by norm_num) (by norm_num) (sr 3 965357 362009 (by norm_num) (by norm_num) (sr 2 362009 271507 (by norm_num) (by norm_num) (sr 1 271507 407261 (by norm_num) (by norm_num) (sr 3 407261 152723 (by norm_num) (by norm_num) (sr 1 152723 229085 (by norm_num) (by norm_num) (sr 3 229085 85907 (by norm_num) (by norm_num) (B 85907 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R100447 : Reach 100447 := (sr 1 100447 150671 (by norm_num) (by norm_num) (sr 1 150671 226007 (by norm_num) (by norm_num) (sr 1 226007 339011 (by norm_num) (by norm_num) (sr 1 339011 508517 (by norm_num) (by norm_num) (sr 4 508517 95347 (by norm_num) (by norm_num) (B 95347 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100451 : Reach 100451 := (sr 1 100451 150677 (by norm_num) (by norm_num) (sr 6 150677 7063 (by norm_num) (by norm_num) (B 7063 (by norm_num) (by norm_num) (by norm_num))))
theorem R100455 : Reach 100455 := (sr 1 100455 150683 (by norm_num) (by norm_num) (sr 1 150683 226025 (by norm_num) (by norm_num) (sr 2 226025 169519 (by norm_num) (by norm_num) (sr 1 169519 254279 (by norm_num) (by norm_num) (sr 1 254279 381419 (by norm_num) (by norm_num) (sr 1 381419 572129 (by norm_num) (by norm_num) (sr 2 572129 429097 (by norm_num) (by norm_num) (sr 2 429097 321823 (by norm_num) (by norm_num) (sr 1 321823 482735 (by norm_num) (by norm_num) (sr 1 482735 724103 (by norm_num) (by norm_num) (sr 1 724103 1086155 (by norm_num) (by norm_num) (sr 1 1086155 1629233 (by norm_num) (by norm_num) (sr 2 1629233 1221925 (by norm_num) (by norm_num) (sr 4 1221925 229111 (by norm_num) (by norm_num) (sr 1 229111 343667 (by norm_num) (by norm_num) (sr 1 343667 515501 (by norm_num) (by norm_num) (sr 3 515501 193313 (by norm_num) (by norm_num) (sr 2 193313 144985 (by norm_num) (by norm_num) (sr 2 144985 108739 (by norm_num) (by norm_num) (sr 1 108739 163109 (by norm_num) (by norm_num) (sr 4 163109 30583 (by norm_num) (by norm_num) (B 30583 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))
theorem R100459 : Reach 100459 := (sr 1 100459 150689 (by norm_num) (by norm_num) (sr 2 150689 113017 (by norm_num) (by norm_num) (sr 2 113017 84763 (by norm_num) (by norm_num) (B 84763 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100463 : Reach 100463 := (sr 1 100463 150695 (by norm_num) (by norm_num) (sr 1 150695 226043 (by norm_num) (by norm_num) (sr 1 226043 339065 (by norm_num) (by norm_num) (sr 2 339065 254299 (by norm_num) (by norm_num) (sr 1 254299 381449 (by norm_num) (by norm_num) (sr 2 381449 286087 (by norm_num) (by norm_num) (sr 1 286087 429131 (by norm_num) (by norm_num) (sr 1 429131 643697 (by norm_num) (by norm_num) (sr 2 643697 482773 (by norm_num) (by norm_num) (sr 7 482773 11315 (by norm_num) (by norm_num) (B 11315 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R100467 : Reach 100467 := (sr 1 100467 150701 (by norm_num) (by norm_num) (sr 3 150701 56513 (by norm_num) (by norm_num) (B 56513 (by norm_num) (by norm_num) (by norm_num))))
theorem R100471 : Reach 100471 := (sr 1 100471 150707 (by norm_num) (by norm_num) (sr 1 150707 226061 (by norm_num) (by norm_num) (sr 3 226061 84773 (by norm_num) (by norm_num) (B 84773 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100475 : Reach 100475 := (sr 1 100475 150713 (by norm_num) (by norm_num) (sr 2 150713 113035 (by norm_num) (by norm_num) (sr 1 113035 169553 (by norm_num) (by norm_num) (sr 2 169553 127165 (by norm_num) (by norm_num) (sr 3 127165 47687 (by norm_num) (by norm_num) (B 47687 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100479 : Reach 100479 := (sr 1 100479 150719 (by norm_num) (by norm_num) (sr 1 150719 226079 (by norm_num) (by norm_num) (sr 1 226079 339119 (by norm_num) (by norm_num) (sr 1 339119 508679 (by norm_num) (by norm_num) (sr 1 508679 763019 (by norm_num) (by norm_num) (sr 1 763019 1144529 (by norm_num) (by norm_num) (sr 2 1144529 858397 (by norm_num) (by norm_num) (sr 3 858397 321899 (by norm_num) (by norm_num) (sr 1 321899 482849 (by norm_num) (by norm_num) (sr 2 482849 362137 (by norm_num) (by norm_num) (sr 2 362137 271603 (by norm_num) (by norm_num) (sr 1 271603 407405 (by norm_num) (by norm_num) (sr 3 407405 152777 (by norm_num) (by norm_num) (sr 2 152777 114583 (by norm_num) (by norm_num) (sr 1 114583 171875 (by norm_num) (by norm_num) (sr 1 171875 257813 (by norm_num) (by norm_num) (sr 6 257813 12085 (by norm_num) (by norm_num) (B 12085 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))
theorem R100483 : Reach 100483 := (sr 1 100483 150725 (by norm_num) (by norm_num) (sr 4 150725 28261 (by norm_num) (by norm_num) (B 28261 (by norm_num) (by norm_num) (by norm_num))))
theorem R100487 : Reach 100487 := (sr 1 100487 150731 (by norm_num) (by norm_num) (sr 1 150731 226097 (by norm_num) (by norm_num) (sr 2 226097 169573 (by norm_num) (by norm_num) (sr 4 169573 31795 (by norm_num) (by norm_num) (B 31795 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100491 : Reach 100491 := (sr 1 100491 150737 (by norm_num) (by norm_num) (sr 2 150737 113053 (by norm_num) (by norm_num) (sr 3 113053 42395 (by norm_num) (by norm_num) (B 42395 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100495 : Reach 100495 := (sr 1 100495 150743 (by norm_num) (by norm_num) (sr 1 150743 226115 (by norm_num) (by norm_num) (sr 1 226115 339173 (by norm_num) (by norm_num) (sr 4 339173 63595 (by norm_num) (by norm_num) (B 63595 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100499 : Reach 100499 := (sr 1 100499 150749 (by norm_num) (by norm_num) (sr 3 150749 56531 (by norm_num) (by norm_num) (B 56531 (by norm_num) (by norm_num) (by norm_num))))
theorem R100503 : Reach 100503 := (sr 1 100503 150755 (by norm_num) (by norm_num) (sr 1 150755 226133 (by norm_num) (by norm_num) (sr 9 226133 1325 (by norm_num) (by norm_num) (B 1325 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100507 : Reach 100507 := (sr 1 100507 150761 (by norm_num) (by norm_num) (sr 2 150761 113071 (by norm_num) (by norm_num) (sr 1 113071 169607 (by norm_num) (by norm_num) (sr 1 169607 254411 (by norm_num) (by norm_num) (sr 1 254411 381617 (by norm_num) (by norm_num) (sr 2 381617 286213 (by norm_num) (by norm_num) (sr 4 286213 53665 (by norm_num) (by norm_num) (B 53665 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R100511 : Reach 100511 := (sr 1 100511 150767 (by norm_num) (by norm_num) (sr 1 150767 226151 (by norm_num) (by norm_num) (sr 1 226151 339227 (by norm_num) (by norm_num) (sr 1 339227 508841 (by norm_num) (by norm_num) (sr 2 508841 381631 (by norm_num) (by norm_num) (sr 1 381631 572447 (by norm_num) (by norm_num) (sr 1 572447 858671 (by norm_num) (by norm_num) (sr 1 858671 1288007 (by norm_num) (by norm_num) (sr 1 1288007 1932011 (by norm_num) (by norm_num) (sr 1 1932011 2898017 (by norm_num) (by norm_num) (sr 2 2898017 2173513 (by norm_num) (by norm_num) (sr 2 2173513 1630135 (by norm_num) (by norm_num) (sr 1 1630135 2445203 (by norm_num) (by norm_num) (sr 1 2445203 3667805 (by norm_num) (by norm_num) (sr 3 3667805 1375427 (by norm_num) (by norm_num) (sr 1 1375427 2063141 (by norm_num) (by norm_num) (sr 4 2063141 386839 (by norm_num) (by norm_num) (sr 1 386839 580259 (by norm_num) (by norm_num) (sr 1 580259 870389 (by norm_num) (by norm_num) (sr 5 870389 81599 (by norm_num) (by norm_num) (B 81599 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))
theorem R100515 : Reach 100515 := (sr 1 100515 150773 (by norm_num) (by norm_num) (sr 5 150773 14135 (by norm_num) (by norm_num) (B 14135 (by norm_num) (by norm_num) (by norm_num))))
theorem R100519 : Reach 100519 := (sr 1 100519 150779 (by norm_num) (by norm_num) (sr 1 150779 226169 (by norm_num) (by norm_num) (sr 2 226169 169627 (by norm_num) (by norm_num) (sr 1 169627 254441 (by norm_num) (by norm_num) (sr 2 254441 190831 (by norm_num) (by norm_num) (sr 1 190831 286247 (by norm_num) (by norm_num) (sr 1 286247 429371 (by norm_num) (by norm_num) (sr 1 429371 644057 (by norm_num) (by norm_num) (sr 2 644057 483043 (by norm_num) (by norm_num) (sr 1 483043 724565 (by norm_num) (by norm_num) (sr 8 724565 8491 (by norm_num) (by norm_num) (B 8491 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R100523 : Reach 100523 := (sr 1 100523 150785 (by norm_num) (by norm_num) (sr 2 150785 113089 (by norm_num) (by norm_num) (sr 2 113089 84817 (by norm_num) (by norm_num) (B 84817 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100527 : Reach 100527 := (sr 1 100527 150791 (by norm_num) (by norm_num) (sr 1 150791 226187 (by norm_num) (by norm_num) (sr 1 226187 339281 (by norm_num) (by norm_num) (sr 2 339281 254461 (by norm_num) (by norm_num) (sr 3 254461 95423 (by norm_num) (by norm_num) (B 95423 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100531 : Reach 100531 := (sr 1 100531 150797 (by norm_num) (by norm_num) (sr 3 150797 56549 (by norm_num) (by norm_num) (B 56549 (by norm_num) (by norm_num) (by norm_num))))
theorem R100535 : Reach 100535 := (sr 1 100535 150803 (by norm_num) (by norm_num) (sr 1 150803 226205 (by norm_num) (by norm_num) (sr 3 226205 84827 (by norm_num) (by norm_num) (B 84827 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100539 : Reach 100539 := (sr 1 100539 150809 (by norm_num) (by norm_num) (sr 2 150809 113107 (by norm_num) (by norm_num) (sr 1 113107 169661 (by norm_num) (by norm_num) (sr 3 169661 63623 (by norm_num) (by norm_num) (B 63623 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100543 : Reach 100543 := (sr 1 100543 150815 (by norm_num) (by norm_num) (sr 1 150815 226223 (by norm_num) (by norm_num) (sr 1 226223 339335 (by norm_num) (by norm_num) (sr 1 339335 509003 (by norm_num) (by norm_num) (sr 1 509003 763505 (by norm_num) (by norm_num) (sr 2 763505 572629 (by norm_num) (by norm_num) (sr 7 572629 13421 (by norm_num) (by norm_num) (B 13421 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R100547 : Reach 100547 := (sr 1 100547 150821 (by norm_num) (by norm_num) (sr 4 150821 28279 (by norm_num) (by norm_num) (B 28279 (by norm_num) (by norm_num) (by norm_num))))
theorem R100551 : Reach 100551 := (sr 1 100551 150827 (by norm_num) (by norm_num) (sr 1 150827 226241 (by norm_num) (by norm_num) (sr 2 226241 169681 (by norm_num) (by norm_num) (sr 2 169681 127261 (by norm_num) (by norm_num) (sr 3 127261 47723 (by norm_num) (by norm_num) (B 47723 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100555 : Reach 100555 := (sr 1 100555 150833 (by norm_num) (by norm_num) (sr 2 150833 113125 (by norm_num) (by norm_num) (sr 4 113125 21211 (by norm_num) (by norm_num) (B 21211 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100559 : Reach 100559 := (sr 1 100559 150839 (by norm_num) (by norm_num) (sr 1 150839 226259 (by norm_num) (by norm_num) (sr 1 226259 339389 (by norm_num) (by norm_num) (sr 3 339389 127271 (by norm_num) (by norm_num) (sr 1 127271 190907 (by norm_num) (by norm_num) (sr 1 190907 286361 (by norm_num) (by norm_num) (sr 2 286361 214771 (by norm_num) (by norm_num) (sr 1 214771 322157 (by norm_num) (by norm_num) (sr 3 322157 120809 (by norm_num) (by norm_num) (sr 2 120809 90607 (by norm_num) (by norm_num) (B 90607 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R100563 : Reach 100563 := (sr 1 100563 150845 (by norm_num) (by norm_num) (sr 3 150845 56567 (by norm_num) (by norm_num) (B 56567 (by norm_num) (by norm_num) (by norm_num))))
theorem R100567 : Reach 100567 := (sr 1 100567 150851 (by norm_num) (by norm_num) (sr 1 150851 226277 (by norm_num) (by norm_num) (sr 4 226277 42427 (by norm_num) (by norm_num) (B 42427 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100571 : Reach 100571 := (sr 1 100571 150857 (by norm_num) (by norm_num) (sr 2 150857 113143 (by norm_num) (by norm_num) (sr 1 113143 169715 (by norm_num) (by norm_num) (sr 1 169715 254573 (by norm_num) (by norm_num) (sr 3 254573 95465 (by norm_num) (by norm_num) (B 95465 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100575 : Reach 100575 := (sr 1 100575 150863 (by norm_num) (by norm_num) (sr 1 150863 226295 (by norm_num) (by norm_num) (sr 1 226295 339443 (by norm_num) (by norm_num) (sr 1 339443 509165 (by norm_num) (by norm_num) (sr 3 509165 190937 (by norm_num) (by norm_num) (sr 2 190937 143203 (by norm_num) (by norm_num) (sr 1 143203 214805 (by norm_num) (by norm_num) (sr 6 214805 10069 (by norm_num) (by norm_num) (B 10069 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R100579 : Reach 100579 := (sr 1 100579 150869 (by norm_num) (by norm_num) (sr 11 150869 221 (by norm_num) (by norm_num) (B 221 (by norm_num) (by norm_num) (by norm_num))))
theorem R100583 : Reach 100583 := (sr 1 100583 150875 (by norm_num) (by norm_num) (sr 1 150875 226313 (by norm_num) (by norm_num) (sr 2 226313 169735 (by norm_num) (by norm_num) (sr 1 169735 254603 (by norm_num) (by norm_num) (sr 1 254603 381905 (by norm_num) (by norm_num) (sr 2 381905 286429 (by norm_num) (by norm_num) (sr 3 286429 107411 (by norm_num) (by norm_num) (sr 1 107411 161117 (by norm_num) (by norm_num) (sr 3 161117 60419 (by norm_num) (by norm_num) (B 60419 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R100587 : Reach 100587 := (sr 1 100587 150881 (by norm_num) (by norm_num) (sr 2 150881 113161 (by norm_num) (by norm_num) (sr 2 113161 84871 (by norm_num) (by norm_num) (B 84871 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100591 : Reach 100591 := (sr 1 100591 150887 (by norm_num) (by norm_num) (sr 1 150887 226331 (by norm_num) (by norm_num) (sr 1 226331 339497 (by norm_num) (by norm_num) (sr 2 339497 254623 (by norm_num) (by norm_num) (sr 1 254623 381935 (by norm_num) (by norm_num) (sr 1 381935 572903 (by norm_num) (by norm_num) (sr 1 572903 859355 (by norm_num) (by norm_num) (sr 1 859355 1289033 (by norm_num) (by norm_num) (sr 2 1289033 966775 (by norm_num) (by norm_num) (sr 1 966775 1450163 (by norm_num) (by norm_num) (sr 1 1450163 2175245 (by norm_num) (by norm_num) (sr 3 2175245 815717 (by norm_num) (by norm_num) (sr 4 815717 152947 (by norm_num) (by norm_num) (sr 1 152947 229421 (by norm_num) (by norm_num) (sr 3 229421 86033 (by norm_num) (by norm_num) (B 86033 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R100595 : Reach 100595 := (sr 1 100595 150893 (by norm_num) (by norm_num) (sr 3 150893 56585 (by norm_num) (by norm_num) (B 56585 (by norm_num) (by norm_num) (by norm_num))))
theorem R100599 : Reach 100599 := (sr 1 100599 150899 (by norm_num) (by norm_num) (sr 1 150899 226349 (by norm_num) (by norm_num) (sr 3 226349 84881 (by norm_num) (by norm_num) (B 84881 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100603 : Reach 100603 := (sr 1 100603 150905 (by norm_num) (by norm_num) (sr 2 150905 113179 (by norm_num) (by norm_num) (sr 1 113179 169769 (by norm_num) (by norm_num) (sr 2 169769 127327 (by norm_num) (by norm_num) (sr 1 127327 190991 (by norm_num) (by norm_num) (sr 1 190991 286487 (by norm_num) (by norm_num) (sr 1 286487 429731 (by norm_num) (by norm_num) (sr 1 429731 644597 (by norm_num) (by norm_num) (sr 5 644597 60431 (by norm_num) (by norm_num) (B 60431 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R100607 : Reach 100607 := (sr 1 100607 150911 (by norm_num) (by norm_num) (sr 1 150911 226367 (by norm_num) (by norm_num) (sr 1 226367 339551 (by norm_num) (by norm_num) (sr 1 339551 509327 (by norm_num) (by norm_num) (sr 1 509327 763991 (by norm_num) (by norm_num) (sr 1 763991 1145987 (by norm_num) (by norm_num) (sr 1 1145987 1718981 (by norm_num) (by norm_num) (sr 4 1718981 322309 (by norm_num) (by norm_num) (sr 4 322309 60433 (by norm_num) (by norm_num) (B 60433 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R100611 : Reach 100611 := (sr 1 100611 150917 (by norm_num) (by norm_num) (sr 4 150917 28297 (by norm_num) (by norm_num) (B 28297 (by norm_num) (by norm_num) (by norm_num))))
theorem R100615 : Reach 100615 := (sr 1 100615 150923 (by norm_num) (by norm_num) (sr 1 150923 226385 (by norm_num) (by norm_num) (sr 2 226385 169789 (by norm_num) (by norm_num) (sr 3 169789 63671 (by norm_num) (by norm_num) (B 63671 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100619 : Reach 100619 := (sr 1 100619 150929 (by norm_num) (by norm_num) (sr 2 150929 113197 (by norm_num) (by norm_num) (sr 3 113197 42449 (by norm_num) (by norm_num) (B 42449 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100623 : Reach 100623 := (sr 1 100623 150935 (by norm_num) (by norm_num) (sr 1 150935 226403 (by norm_num) (by norm_num) (sr 1 226403 339605 (by norm_num) (by norm_num) (sr 6 339605 15919 (by norm_num) (by norm_num) (B 15919 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100627 : Reach 100627 := (sr 1 100627 150941 (by norm_num) (by norm_num) (sr 3 150941 56603 (by norm_num) (by norm_num) (B 56603 (by norm_num) (by norm_num) (by norm_num))))
theorem R100631 : Reach 100631 := (sr 1 100631 150947 (by norm_num) (by norm_num) (sr 1 150947 226421 (by norm_num) (by norm_num) (sr 5 226421 21227 (by norm_num) (by norm_num) (B 21227 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100635 : Reach 100635 := (sr 1 100635 150953 (by norm_num) (by norm_num) (sr 2 150953 113215 (by norm_num) (by norm_num) (sr 1 113215 169823 (by norm_num) (by norm_num) (sr 1 169823 254735 (by norm_num) (by norm_num) (sr 1 254735 382103 (by norm_num) (by norm_num) (sr 1 382103 573155 (by norm_num) (by norm_num) (sr 1 573155 859733 (by norm_num) (by norm_num) (sr 8 859733 10075 (by norm_num) (by norm_num) (B 10075 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R100639 : Reach 100639 := (sr 1 100639 150959 (by norm_num) (by norm_num) (sr 1 150959 226439 (by norm_num) (by norm_num) (sr 1 226439 339659 (by norm_num) (by norm_num) (sr 1 339659 509489 (by norm_num) (by norm_num) (sr 2 509489 382117 (by norm_num) (by norm_num) (sr 4 382117 71647 (by norm_num) (by norm_num) (B 71647 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R100643 : Reach 100643 := (sr 1 100643 150965 (by norm_num) (by norm_num) (sr 5 150965 14153 (by norm_num) (by norm_num) (B 14153 (by norm_num) (by norm_num) (by norm_num))))
theorem R100647 : Reach 100647 := (sr 1 100647 150971 (by norm_num) (by norm_num) (sr 1 150971 226457 (by norm_num) (by norm_num) (sr 2 226457 169843 (by norm_num) (by norm_num) (sr 1 169843 254765 (by norm_num) (by norm_num) (sr 3 254765 95537 (by norm_num) (by norm_num) (B 95537 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100651 : Reach 100651 := (sr 1 100651 150977 (by norm_num) (by norm_num) (sr 2 150977 113233 (by norm_num) (by norm_num) (sr 2 113233 84925 (by norm_num) (by norm_num) (B 84925 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100655 : Reach 100655 := (sr 1 100655 150983 (by norm_num) (by norm_num) (sr 1 150983 226475 (by norm_num) (by norm_num) (sr 1 226475 339713 (by norm_num) (by norm_num) (sr 2 339713 254785 (by norm_num) (by norm_num) (sr 2 254785 191089 (by norm_num) (by norm_num) (sr 2 191089 143317 (by norm_num) (by norm_num) (sr 7 143317 3359 (by norm_num) (by norm_num) (B 3359 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R100659 : Reach 100659 := (sr 1 100659 150989 (by norm_num) (by norm_num) (sr 3 150989 56621 (by norm_num) (by norm_num) (B 56621 (by norm_num) (by norm_num) (by norm_num))))
theorem R100663 : Reach 100663 := (sr 1 100663 150995 (by norm_num) (by norm_num) (sr 1 150995 226493 (by norm_num) (by norm_num) (sr 3 226493 84935 (by norm_num) (by norm_num) (B 84935 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100667 : Reach 100667 := (sr 1 100667 151001 (by norm_num) (by norm_num) (sr 2 151001 113251 (by norm_num) (by norm_num) (sr 1 113251 169877 (by norm_num) (by norm_num) (sr 6 169877 7963 (by norm_num) (by norm_num) (B 7963 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100671 : Reach 100671 := (sr 1 100671 151007 (by norm_num) (by norm_num) (sr 1 151007 226511 (by norm_num) (by norm_num) (sr 1 226511 339767 (by norm_num) (by norm_num) (sr 1 339767 509651 (by norm_num) (by norm_num) (sr 1 509651 764477 (by norm_num) (by norm_num) (sr 3 764477 286679 (by norm_num) (by norm_num) (sr 1 286679 430019 (by norm_num) (by norm_num) (sr 1 430019 645029 (by norm_num) (by norm_num) (sr 4 645029 120943 (by norm_num) (by norm_num) (sr 1 120943 181415 (by norm_num) (by norm_num) (sr 1 181415 272123 (by norm_num) (by norm_num) (sr 1 272123 408185 (by norm_num) (by norm_num) (sr 2 408185 306139 (by norm_num) (by norm_num) (sr 1 306139 459209 (by norm_num) (by norm_num) (sr 2 459209 344407 (by norm_num) (by norm_num) (sr 1 344407 516611 (by norm_num) (by norm_num) (sr 1 516611 774917 (by norm_num) (by norm_num) (sr 4 774917 145297 (by norm_num) (by norm_num) (sr 2 145297 108973 (by norm_num) (by norm_num) (sr 3 108973 40865 (by norm_num) (by norm_num) (B 40865 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))
theorem R100675 : Reach 100675 := (sr 1 100675 151013 (by norm_num) (by norm_num) (sr 4 151013 28315 (by norm_num) (by norm_num) (B 28315 (by norm_num) (by norm_num) (by norm_num))))
theorem R100679 : Reach 100679 := (sr 1 100679 151019 (by norm_num) (by norm_num) (sr 1 151019 226529 (by norm_num) (by norm_num) (sr 2 226529 169897 (by norm_num) (by norm_num) (sr 2 169897 127423 (by norm_num) (by norm_num) (sr 1 127423 191135 (by norm_num) (by norm_num) (sr 1 191135 286703 (by norm_num) (by norm_num) (sr 1 286703 430055 (by norm_num) (by norm_num) (sr 1 430055 645083 (by norm_num) (by norm_num) (sr 1 645083 967625 (by norm_num) (by norm_num) (sr 2 967625 725719 (by norm_num) (by norm_num) (sr 1 725719 1088579 (by norm_num) (by norm_num) (sr 1 1088579 1632869 (by norm_num) (by norm_num) (sr 4 1632869 306163 (by norm_num) (by norm_num) (sr 1 306163 459245 (by norm_num) (by norm_num) (sr 3 459245 172217 (by norm_num) (by norm_num) (sr 2 172217 129163 (by norm_num) (by norm_num) (sr 1 129163 193745 (by norm_num) (by norm_num) (sr 2 193745 145309 (by norm_num) (by norm_num) (sr 3 145309 54491 (by norm_num) (by norm_num) (B 54491 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))
theorem R100683 : Reach 100683 := (sr 1 100683 151025 (by norm_num) (by norm_num) (sr 2 151025 113269 (by norm_num) (by norm_num) (sr 5 113269 10619 (by norm_num) (by norm_num) (B 10619 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100687 : Reach 100687 := (sr 1 100687 151031 (by norm_num) (by norm_num) (sr 1 151031 226547 (by norm_num) (by norm_num) (sr 1 226547 339821 (by norm_num) (by norm_num) (sr 3 339821 127433 (by norm_num) (by norm_num) (sr 2 127433 95575 (by norm_num) (by norm_num) (B 95575 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100691 : Reach 100691 := (sr 1 100691 151037 (by norm_num) (by norm_num) (sr 3 151037 56639 (by norm_num) (by norm_num) (B 56639 (by norm_num) (by norm_num) (by norm_num))))
theorem R100695 : Reach 100695 := (sr 1 100695 151043 (by norm_num) (by norm_num) (sr 1 151043 226565 (by norm_num) (by norm_num) (sr 4 226565 42481 (by norm_num) (by norm_num) (B 42481 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100699 : Reach 100699 := (sr 1 100699 151049 (by norm_num) (by norm_num) (sr 2 151049 113287 (by norm_num) (by norm_num) (sr 1 113287 169931 (by norm_num) (by norm_num) (sr 1 169931 254897 (by norm_num) (by norm_num) (sr 2 254897 191173 (by norm_num) (by norm_num) (sr 4 191173 35845 (by norm_num) (by norm_num) (B 35845 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R100703 : Reach 100703 := (sr 1 100703 151055 (by norm_num) (by norm_num) (sr 1 151055 226583 (by norm_num) (by norm_num) (sr 1 226583 339875 (by norm_num) (by norm_num) (sr 1 339875 509813 (by norm_num) (by norm_num) (sr 5 509813 47795 (by norm_num) (by norm_num) (B 47795 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100707 : Reach 100707 := (sr 1 100707 151061 (by norm_num) (by norm_num) (sr 6 151061 7081 (by norm_num) (by norm_num) (B 7081 (by norm_num) (by norm_num) (by norm_num))))
theorem R100711 : Reach 100711 := (sr 1 100711 151067 (by norm_num) (by norm_num) (sr 1 151067 226601 (by norm_num) (by norm_num) (sr 2 226601 169951 (by norm_num) (by norm_num) (sr 1 169951 254927 (by norm_num) (by norm_num) (sr 1 254927 382391 (by norm_num) (by norm_num) (sr 1 382391 573587 (by norm_num) (by norm_num) (sr 1 573587 860381 (by norm_num) (by norm_num) (sr 3 860381 322643 (by norm_num) (by norm_num) (sr 1 322643 483965 (by norm_num) (by norm_num) (sr 3 483965 181487 (by norm_num) (by norm_num) (sr 1 181487 272231 (by norm_num) (by norm_num) (sr 1 272231 408347 (by norm_num) (by norm_num) (sr 1 408347 612521 (by norm_num) (by norm_num) (sr 2 612521 459391 (by norm_num) (by norm_num) (sr 1 459391 689087 (by norm_num) (by norm_num) (sr 1 689087 1033631 (by norm_num) (by norm_num) (sr 1 1033631 1550447 (by norm_num) (by norm_num) (sr 1 1550447 2325671 (by norm_num) (by norm_num) (sr 1 2325671 3488507 (by norm_num) (by norm_num) (sr 1 3488507 5232761 (by norm_num) (by norm_num) (sr 2 5232761 3924571 (by norm_num) (by norm_num) (sr 1 3924571 5886857 (by norm_num) (by norm_num) (sr 2 5886857 4415143 (by norm_num) (by norm_num) (sr 1 4415143 6622715 (by norm_num) (by norm_num) (sr 1 6622715 9934073 (by norm_num) (by norm_num) (sr 2 9934073 7450555 (by norm_num) (by norm_num) (sr 1 7450555 11175833 (by norm_num) (by norm_num) (sr 2 11175833 8381875 (by norm_num) (by norm_num) (sr 1 8381875 12572813 (by norm_num) (by norm_num) (sr 3 12572813 4714805 (by norm_num) (by norm_num) (sr 5 4714805 442013 (by norm_num) (by norm_num) (sr 3 442013 165755 (by norm_num) (by norm_num) (sr 1 165755 248633 (by norm_num) (by norm_num) (sr 2 248633 186475 (by norm_num) (by norm_num) (sr 1 186475 279713 (by norm_num) (by norm_num) (sr 2 279713 209785 (by norm_num) (by norm_num) (sr 2 209785 157339 (by norm_num) (by norm_num) (sr 1 157339 236009 (by norm_num) (by norm_num) (sr 2 236009 177007 (by norm_num) (by norm_num) (sr 1 177007 265511 (by norm_num) (by norm_num) (sr 1 265511 398267 (by norm_num) (by norm_num) (sr 1 398267 597401 (by norm_num) (by norm_num) (sr 2 597401 448051 (by norm_num) (by norm_num) (sr 1 448051 672077 (by norm_num) (by norm_num) (sr 3 672077 252029 (by norm_num) (by norm_num) (sr 3 252029 94511 (by norm_num) (by norm_num) (B 94511 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))))))))))))))))))))
theorem R100715 : Reach 100715 := (sr 1 100715 151073 (by norm_num) (by norm_num) (sr 2 151073 113305 (by norm_num) (by norm_num) (sr 2 113305 84979 (by norm_num) (by norm_num) (B 84979 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100719 : Reach 100719 := (sr 1 100719 151079 (by norm_num) (by norm_num) (sr 1 151079 226619 (by norm_num) (by norm_num) (sr 1 226619 339929 (by norm_num) (by norm_num) (sr 2 339929 254947 (by norm_num) (by norm_num) (sr 1 254947 382421 (by norm_num) (by norm_num) (sr 7 382421 8963 (by norm_num) (by norm_num) (B 8963 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R100723 : Reach 100723 := (sr 1 100723 151085 (by norm_num) (by norm_num) (sr 3 151085 56657 (by norm_num) (by norm_num) (B 56657 (by norm_num) (by norm_num) (by norm_num))))
theorem R100727 : Reach 100727 := (sr 1 100727 151091 (by norm_num) (by norm_num) (sr 1 151091 226637 (by norm_num) (by norm_num) (sr 3 226637 84989 (by norm_num) (by norm_num) (B 84989 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100731 : Reach 100731 := (sr 1 100731 151097 (by norm_num) (by norm_num) (sr 2 151097 113323 (by norm_num) (by norm_num) (sr 1 113323 169985 (by norm_num) (by norm_num) (sr 2 169985 127489 (by norm_num) (by norm_num) (sr 2 127489 95617 (by norm_num) (by norm_num) (B 95617 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100735 : Reach 100735 := (sr 1 100735 151103 (by norm_num) (by norm_num) (sr 1 151103 226655 (by norm_num) (by norm_num) (sr 1 226655 339983 (by norm_num) (by norm_num) (sr 1 339983 509975 (by norm_num) (by norm_num) (sr 1 509975 764963 (by norm_num) (by norm_num) (sr 1 764963 1147445 (by norm_num) (by norm_num) (sr 5 1147445 107573 (by norm_num) (by norm_num) (sr 5 107573 10085 (by norm_num) (by norm_num) (B 10085 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R100739 : Reach 100739 := (sr 1 100739 151109 (by norm_num) (by norm_num) (sr 4 151109 28333 (by norm_num) (by norm_num) (B 28333 (by norm_num) (by norm_num) (by norm_num))))
theorem R100743 : Reach 100743 := (sr 1 100743 151115 (by norm_num) (by norm_num) (sr 1 151115 226673 (by norm_num) (by norm_num) (sr 2 226673 170005 (by norm_num) (by norm_num) (sr 6 170005 7969 (by norm_num) (by norm_num) (B 7969 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100747 : Reach 100747 := (sr 1 100747 151121 (by norm_num) (by norm_num) (sr 2 151121 113341 (by norm_num) (by norm_num) (sr 3 113341 42503 (by norm_num) (by norm_num) (B 42503 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100751 : Reach 100751 := (sr 1 100751 151127 (by norm_num) (by norm_num) (sr 1 151127 226691 (by norm_num) (by norm_num) (sr 1 226691 340037 (by norm_num) (by norm_num) (sr 4 340037 63757 (by norm_num) (by norm_num) (B 63757 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100755 : Reach 100755 := (sr 1 100755 151133 (by norm_num) (by norm_num) (sr 3 151133 56675 (by norm_num) (by norm_num) (B 56675 (by norm_num) (by norm_num) (by norm_num))))
theorem R100759 : Reach 100759 := (sr 1 100759 151139 (by norm_num) (by norm_num) (sr 1 151139 226709 (by norm_num) (by norm_num) (sr 6 226709 10627 (by norm_num) (by norm_num) (B 10627 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100763 : Reach 100763 := (sr 1 100763 151145 (by norm_num) (by norm_num) (sr 2 151145 113359 (by norm_num) (by norm_num) (sr 1 113359 170039 (by norm_num) (by norm_num) (sr 1 170039 255059 (by norm_num) (by norm_num) (sr 1 255059 382589 (by norm_num) (by norm_num) (sr 3 382589 143471 (by norm_num) (by norm_num) (sr 1 143471 215207 (by norm_num) (by norm_num) (sr 1 215207 322811 (by norm_num) (by norm_num) (sr 1 322811 484217 (by norm_num) (by norm_num) (sr 2 484217 363163 (by norm_num) (by norm_num) (sr 1 363163 544745 (by norm_num) (by norm_num) (sr 2 544745 408559 (by norm_num) (by norm_num) (sr 1 408559 612839 (by norm_num) (by norm_num) (sr 1 612839 919259 (by norm_num) (by norm_num) (sr 1 919259 1378889 (by norm_num) (by norm_num) (sr 2 1378889 1034167 (by norm_num) (by norm_num) (sr 1 1034167 1551251 (by norm_num) (by norm_num) (sr 1 1551251 2326877 (by norm_num) (by norm_num) (sr 3 2326877 872579 (by norm_num) (by norm_num) (sr 1 872579 1308869 (by norm_num) (by norm_num) (sr 4 1308869 245413 (by norm_num) (by norm_num) (sr 4 245413 46015 (by norm_num) (by norm_num) (B 46015 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R100767 : Reach 100767 := (sr 1 100767 151151 (by norm_num) (by norm_num) (sr 1 151151 226727 (by norm_num) (by norm_num) (sr 1 226727 340091 (by norm_num) (by norm_num) (sr 1 340091 510137 (by norm_num) (by norm_num) (sr 2 510137 382603 (by norm_num) (by norm_num) (sr 1 382603 573905 (by norm_num) (by norm_num) (sr 2 573905 430429 (by norm_num) (by norm_num) (sr 3 430429 161411 (by norm_num) (by norm_num) (sr 1 161411 242117 (by norm_num) (by norm_num) (sr 4 242117 45397 (by norm_num) (by norm_num) (B 45397 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R100771 : Reach 100771 := (sr 1 100771 151157 (by norm_num) (by norm_num) (sr 5 151157 14171 (by norm_num) (by norm_num) (B 14171 (by norm_num) (by norm_num) (by norm_num))))
theorem R100775 : Reach 100775 := (sr 1 100775 151163 (by norm_num) (by norm_num) (sr 1 151163 226745 (by norm_num) (by norm_num) (sr 2 226745 170059 (by norm_num) (by norm_num) (sr 1 170059 255089 (by norm_num) (by norm_num) (sr 2 255089 191317 (by norm_num) (by norm_num) (sr 9 191317 1121 (by norm_num) (by norm_num) (B 1121 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R100779 : Reach 100779 := (sr 1 100779 151169 (by norm_num) (by norm_num) (sr 2 151169 113377 (by norm_num) (by norm_num) (sr 2 113377 85033 (by norm_num) (by norm_num) (B 85033 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100783 : Reach 100783 := (sr 1 100783 151175 (by norm_num) (by norm_num) (sr 1 151175 226763 (by norm_num) (by norm_num) (sr 1 226763 340145 (by norm_num) (by norm_num) (sr 2 340145 255109 (by norm_num) (by norm_num) (sr 4 255109 47833 (by norm_num) (by norm_num) (B 47833 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100787 : Reach 100787 := (sr 1 100787 151181 (by norm_num) (by norm_num) (sr 3 151181 56693 (by norm_num) (by norm_num) (B 56693 (by norm_num) (by norm_num) (by norm_num))))
theorem R100791 : Reach 100791 := (sr 1 100791 151187 (by norm_num) (by norm_num) (sr 1 151187 226781 (by norm_num) (by norm_num) (sr 3 226781 85043 (by norm_num) (by norm_num) (B 85043 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100795 : Reach 100795 := (sr 1 100795 151193 (by norm_num) (by norm_num) (sr 2 151193 113395 (by norm_num) (by norm_num) (sr 1 113395 170093 (by norm_num) (by norm_num) (sr 3 170093 63785 (by norm_num) (by norm_num) (B 63785 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100799 : Reach 100799 := (sr 1 100799 151199 (by norm_num) (by norm_num) (sr 1 151199 226799 (by norm_num) (by norm_num) (sr 1 226799 340199 (by norm_num) (by norm_num) (sr 1 340199 510299 (by norm_num) (by norm_num) (sr 1 510299 765449 (by norm_num) (by norm_num) (sr 2 765449 574087 (by norm_num) (by norm_num) (sr 1 574087 861131 (by norm_num) (by norm_num) (sr 1 861131 1291697 (by norm_num) (by norm_num) (sr 2 1291697 968773 (by norm_num) (by norm_num) (sr 4 968773 181645 (by norm_num) (by norm_num) (sr 3 181645 68117 (by norm_num) (by norm_num) (B 68117 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R100803 : Reach 100803 := (sr 1 100803 151205 (by norm_num) (by norm_num) (sr 4 151205 28351 (by norm_num) (by norm_num) (B 28351 (by norm_num) (by norm_num) (by norm_num))))
theorem R100807 : Reach 100807 := (sr 1 100807 151211 (by norm_num) (by norm_num) (sr 1 151211 226817 (by norm_num) (by norm_num) (sr 2 226817 170113 (by norm_num) (by norm_num) (sr 2 170113 127585 (by norm_num) (by norm_num) (sr 2 127585 95689 (by norm_num) (by norm_num) (B 95689 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100811 : Reach 100811 := (sr 1 100811 151217 (by norm_num) (by norm_num) (sr 2 151217 113413 (by norm_num) (by norm_num) (sr 4 113413 21265 (by norm_num) (by norm_num) (B 21265 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100815 : Reach 100815 := (sr 1 100815 151223 (by norm_num) (by norm_num) (sr 1 151223 226835 (by norm_num) (by norm_num) (sr 1 226835 340253 (by norm_num) (by norm_num) (sr 3 340253 127595 (by norm_num) (by norm_num) (sr 1 127595 191393 (by norm_num) (by norm_num) (sr 2 191393 143545 (by norm_num) (by norm_num) (sr 2 143545 107659 (by norm_num) (by norm_num) (sr 1 107659 161489 (by norm_num) (by norm_num) (sr 2 161489 121117 (by norm_num) (by norm_num) (sr 3 121117 45419 (by norm_num) (by norm_num) (B 45419 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R100819 : Reach 100819 := (sr 1 100819 151229 (by norm_num) (by norm_num) (sr 3 151229 56711 (by norm_num) (by norm_num) (B 56711 (by norm_num) (by norm_num) (by norm_num))))
theorem R100823 : Reach 100823 := (sr 1 100823 151235 (by norm_num) (by norm_num) (sr 1 151235 226853 (by norm_num) (by norm_num) (sr 4 226853 42535 (by norm_num) (by norm_num) (B 42535 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100827 : Reach 100827 := (sr 1 100827 151241 (by norm_num) (by norm_num) (sr 2 151241 113431 (by norm_num) (by norm_num) (sr 1 113431 170147 (by norm_num) (by norm_num) (sr 1 170147 255221 (by norm_num) (by norm_num) (sr 5 255221 23927 (by norm_num) (by norm_num) (B 23927 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100831 : Reach 100831 := (sr 1 100831 151247 (by norm_num) (by norm_num) (sr 1 151247 226871 (by norm_num) (by norm_num) (sr 1 226871 340307 (by norm_num) (by norm_num) (sr 1 340307 510461 (by norm_num) (by norm_num) (sr 3 510461 191423 (by norm_num) (by norm_num) (sr 1 191423 287135 (by norm_num) (by norm_num) (sr 1 287135 430703 (by norm_num) (by norm_num) (sr 1 430703 646055 (by norm_num) (by norm_num) (sr 1 646055 969083 (by norm_num) (by norm_num) (sr 1 969083 1453625 (by norm_num) (by norm_num) (sr 2 1453625 1090219 (by norm_num) (by norm_num) (sr 1 1090219 1635329 (by norm_num) (by norm_num) (sr 2 1635329 1226497 (by norm_num) (by norm_num) (sr 2 1226497 919873 (by norm_num) (by norm_num) (sr 2 919873 689905 (by norm_num) (by norm_num) (sr 2 689905 517429 (by norm_num) (by norm_num) (sr 5 517429 48509 (by norm_num) (by norm_num) (B 48509 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))
theorem R100835 : Reach 100835 := (sr 1 100835 151253 (by norm_num) (by norm_num) (sr 7 151253 3545 (by norm_num) (by norm_num) (B 3545 (by norm_num) (by norm_num) (by norm_num))))
theorem R100839 : Reach 100839 := (sr 1 100839 151259 (by norm_num) (by norm_num) (sr 1 151259 226889 (by norm_num) (by norm_num) (sr 2 226889 170167 (by norm_num) (by norm_num) (sr 1 170167 255251 (by norm_num) (by norm_num) (sr 1 255251 382877 (by norm_num) (by norm_num) (sr 3 382877 143579 (by norm_num) (by norm_num) (sr 1 143579 215369 (by norm_num) (by norm_num) (sr 2 215369 161527 (by norm_num) (by norm_num) (sr 1 161527 242291 (by norm_num) (by norm_num) (sr 1 242291 363437 (by norm_num) (by norm_num) (sr 3 363437 136289 (by norm_num) (by norm_num) (sr 2 136289 102217 (by norm_num) (by norm_num) (sr 2 102217 76663 (by norm_num) (by norm_num) (B 76663 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R100843 : Reach 100843 := (sr 1 100843 151265 (by norm_num) (by norm_num) (sr 2 151265 113449 (by norm_num) (by norm_num) (sr 2 113449 85087 (by norm_num) (by norm_num) (B 85087 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100847 : Reach 100847 := (sr 1 100847 151271 (by norm_num) (by norm_num) (sr 1 151271 226907 (by norm_num) (by norm_num) (sr 1 226907 340361 (by norm_num) (by norm_num) (sr 2 340361 255271 (by norm_num) (by norm_num) (sr 1 255271 382907 (by norm_num) (by norm_num) (sr 1 382907 574361 (by norm_num) (by norm_num) (sr 2 574361 430771 (by norm_num) (by norm_num) (sr 1 430771 646157 (by norm_num) (by norm_num) (sr 3 646157 242309 (by norm_num) (by norm_num) (sr 4 242309 45433 (by norm_num) (by norm_num) (B 45433 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R100851 : Reach 100851 := (sr 1 100851 151277 (by norm_num) (by norm_num) (sr 3 151277 56729 (by norm_num) (by norm_num) (B 56729 (by norm_num) (by norm_num) (by norm_num))))
theorem R100855 : Reach 100855 := (sr 1 100855 151283 (by norm_num) (by norm_num) (sr 1 151283 226925 (by norm_num) (by norm_num) (sr 3 226925 85097 (by norm_num) (by norm_num) (B 85097 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100859 : Reach 100859 := (sr 1 100859 151289 (by norm_num) (by norm_num) (sr 2 151289 113467 (by norm_num) (by norm_num) (sr 1 113467 170201 (by norm_num) (by norm_num) (sr 2 170201 127651 (by norm_num) (by norm_num) (sr 1 127651 191477 (by norm_num) (by norm_num) (sr 5 191477 17951 (by norm_num) (by norm_num) (B 17951 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R100863 : Reach 100863 := (sr 1 100863 151295 (by norm_num) (by norm_num) (sr 1 151295 226943 (by norm_num) (by norm_num) (sr 1 226943 340415 (by norm_num) (by norm_num) (sr 1 340415 510623 (by norm_num) (by norm_num) (sr 1 510623 765935 (by norm_num) (by norm_num) (sr 1 765935 1148903 (by norm_num) (by norm_num) (sr 1 1148903 1723355 (by norm_num) (by norm_num) (sr 1 1723355 2585033 (by norm_num) (by norm_num) (sr 2 2585033 1938775 (by norm_num) (by norm_num) (sr 1 1938775 2908163 (by norm_num) (by norm_num) (sr 1 2908163 4362245 (by norm_num) (by norm_num) (sr 4 4362245 817921 (by norm_num) (by norm_num) (sr 2 817921 613441 (by norm_num) (by norm_num) (sr 2 613441 460081 (by norm_num) (by norm_num) (sr 2 460081 345061 (by norm_num) (by norm_num) (sr 4 345061 64699 (by norm_num) (by norm_num) (B 64699 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))
theorem R100867 : Reach 100867 := (sr 1 100867 151301 (by norm_num) (by norm_num) (sr 4 151301 28369 (by norm_num) (by norm_num) (B 28369 (by norm_num) (by norm_num) (by norm_num))))
theorem R100871 : Reach 100871 := (sr 1 100871 151307 (by norm_num) (by norm_num) (sr 1 151307 226961 (by norm_num) (by norm_num) (sr 2 226961 170221 (by norm_num) (by norm_num) (sr 3 170221 63833 (by norm_num) (by norm_num) (B 63833 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100875 : Reach 100875 := (sr 1 100875 151313 (by norm_num) (by norm_num) (sr 2 151313 113485 (by norm_num) (by norm_num) (sr 3 113485 42557 (by norm_num) (by norm_num) (B 42557 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100879 : Reach 100879 := (sr 1 100879 151319 (by norm_num) (by norm_num) (sr 1 151319 226979 (by norm_num) (by norm_num) (sr 1 226979 340469 (by norm_num) (by norm_num) (sr 5 340469 31919 (by norm_num) (by norm_num) (B 31919 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100883 : Reach 100883 := (sr 1 100883 151325 (by norm_num) (by norm_num) (sr 3 151325 56747 (by norm_num) (by norm_num) (B 56747 (by norm_num) (by norm_num) (by norm_num))))
theorem R100887 : Reach 100887 := (sr 1 100887 151331 (by norm_num) (by norm_num) (sr 1 151331 226997 (by norm_num) (by norm_num) (sr 5 226997 21281 (by norm_num) (by norm_num) (B 21281 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100891 : Reach 100891 := (sr 1 100891 151337 (by norm_num) (by norm_num) (sr 2 151337 113503 (by norm_num) (by norm_num) (sr 1 113503 170255 (by norm_num) (by norm_num) (sr 1 170255 255383 (by norm_num) (by norm_num) (sr 1 255383 383075 (by norm_num) (by norm_num) (sr 1 383075 574613 (by norm_num) (by norm_num) (sr 6 574613 26935 (by norm_num) (by norm_num) (B 26935 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R100895 : Reach 100895 := (sr 1 100895 151343 (by norm_num) (by norm_num) (sr 1 151343 227015 (by norm_num) (by norm_num) (sr 1 227015 340523 (by norm_num) (by norm_num) (sr 1 340523 510785 (by norm_num) (by norm_num) (sr 2 510785 383089 (by norm_num) (by norm_num) (sr 2 383089 287317 (by norm_num) (by norm_num) (sr 8 287317 3367 (by norm_num) (by norm_num) (B 3367 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R100899 : Reach 100899 := (sr 1 100899 151349 (by norm_num) (by norm_num) (sr 5 151349 14189 (by norm_num) (by norm_num) (B 14189 (by norm_num) (by norm_num) (by norm_num))))
theorem R100903 : Reach 100903 := (sr 1 100903 151355 (by norm_num) (by norm_num) (sr 1 151355 227033 (by norm_num) (by norm_num) (sr 2 227033 170275 (by norm_num) (by norm_num) (sr 1 170275 255413 (by norm_num) (by norm_num) (sr 5 255413 23945 (by norm_num) (by norm_num) (B 23945 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100907 : Reach 100907 := (sr 1 100907 151361 (by norm_num) (by norm_num) (sr 2 151361 113521 (by norm_num) (by norm_num) (sr 2 113521 85141 (by norm_num) (by norm_num) (B 85141 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100911 : Reach 100911 := (sr 1 100911 151367 (by norm_num) (by norm_num) (sr 1 151367 227051 (by norm_num) (by norm_num) (sr 1 227051 340577 (by norm_num) (by norm_num) (sr 2 340577 255433 (by norm_num) (by norm_num) (sr 2 255433 191575 (by norm_num) (by norm_num) (sr 1 191575 287363 (by norm_num) (by norm_num) (sr 1 287363 431045 (by norm_num) (by norm_num) (sr 4 431045 80821 (by norm_num) (by norm_num) (B 80821 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R100915 : Reach 100915 := (sr 1 100915 151373 (by norm_num) (by norm_num) (sr 3 151373 56765 (by norm_num) (by norm_num) (B 56765 (by norm_num) (by norm_num) (by norm_num))))
theorem R100919 : Reach 100919 := (sr 1 100919 151379 (by norm_num) (by norm_num) (sr 1 151379 227069 (by norm_num) (by norm_num) (sr 3 227069 85151 (by norm_num) (by norm_num) (B 85151 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100923 : Reach 100923 := (sr 1 100923 151385 (by norm_num) (by norm_num) (sr 2 151385 113539 (by norm_num) (by norm_num) (sr 1 113539 170309 (by norm_num) (by norm_num) (sr 4 170309 31933 (by norm_num) (by norm_num) (B 31933 (by norm_num) (by norm_num) (by norm_num))))))
theorem R100927 : Reach 100927 := (sr 1 100927 151391 (by norm_num) (by norm_num) (sr 1 151391 227087 (by norm_num) (by norm_num) (sr 1 227087 340631 (by norm_num) (by norm_num) (sr 1 340631 510947 (by norm_num) (by norm_num) (sr 1 510947 766421 (by norm_num) (by norm_num) (sr 7 766421 17963 (by norm_num) (by norm_num) (B 17963 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R100931 : Reach 100931 := (sr 1 100931 151397 (by norm_num) (by norm_num) (sr 4 151397 28387 (by norm_num) (by norm_num) (B 28387 (by norm_num) (by norm_num) (by norm_num))))
theorem R100935 : Reach 100935 := (sr 1 100935 151403 (by norm_num) (by norm_num) (sr 1 151403 227105 (by norm_num) (by norm_num) (sr 2 227105 170329 (by norm_num) (by norm_num) (sr 2 170329 127747 (by norm_num) (by norm_num) (sr 1 127747 191621 (by norm_num) (by norm_num) (sr 4 191621 35929 (by norm_num) (by norm_num) (B 35929 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R100939 : Reach 100939 := (sr 1 100939 151409 (by norm_num) (by norm_num) (sr 2 151409 113557 (by norm_num) (by norm_num) (sr 6 113557 5323 (by norm_num) (by norm_num) (B 5323 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100943 : Reach 100943 := (sr 1 100943 151415 (by norm_num) (by norm_num) (sr 1 151415 227123 (by norm_num) (by norm_num) (sr 1 227123 340685 (by norm_num) (by norm_num) (sr 3 340685 127757 (by norm_num) (by norm_num) (sr 3 127757 47909 (by norm_num) (by norm_num) (B 47909 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100947 : Reach 100947 := (sr 1 100947 151421 (by norm_num) (by norm_num) (sr 3 151421 56783 (by norm_num) (by norm_num) (B 56783 (by norm_num) (by norm_num) (by norm_num))))
theorem R100951 : Reach 100951 := (sr 1 100951 151427 (by norm_num) (by norm_num) (sr 1 151427 227141 (by norm_num) (by norm_num) (sr 4 227141 42589 (by norm_num) (by norm_num) (B 42589 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100955 : Reach 100955 := (sr 1 100955 151433 (by norm_num) (by norm_num) (sr 2 151433 113575 (by norm_num) (by norm_num) (sr 1 113575 170363 (by norm_num) (by norm_num) (sr 1 170363 255545 (by norm_num) (by norm_num) (sr 2 255545 191659 (by norm_num) (by norm_num) (sr 1 191659 287489 (by norm_num) (by norm_num) (sr 2 287489 215617 (by norm_num) (by norm_num) (sr 2 215617 161713 (by norm_num) (by norm_num) (sr 2 161713 121285 (by norm_num) (by norm_num) (sr 4 121285 22741 (by norm_num) (by norm_num) (B 22741 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R100959 : Reach 100959 := (sr 1 100959 151439 (by norm_num) (by norm_num) (sr 1 151439 227159 (by norm_num) (by norm_num) (sr 1 227159 340739 (by norm_num) (by norm_num) (sr 1 340739 511109 (by norm_num) (by norm_num) (sr 4 511109 95833 (by norm_num) (by norm_num) (B 95833 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100963 : Reach 100963 := (sr 1 100963 151445 (by norm_num) (by norm_num) (sr 6 151445 7099 (by norm_num) (by norm_num) (B 7099 (by norm_num) (by norm_num) (by norm_num))))
theorem R100967 : Reach 100967 := (sr 1 100967 151451 (by norm_num) (by norm_num) (sr 1 151451 227177 (by norm_num) (by norm_num) (sr 2 227177 170383 (by norm_num) (by norm_num) (sr 1 170383 255575 (by norm_num) (by norm_num) (sr 1 255575 383363 (by norm_num) (by norm_num) (sr 1 383363 575045 (by norm_num) (by norm_num) (sr 4 575045 107821 (by norm_num) (by norm_num) (sr 3 107821 40433 (by norm_num) (by norm_num) (B 40433 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R100971 : Reach 100971 := (sr 1 100971 151457 (by norm_num) (by norm_num) (sr 2 151457 113593 (by norm_num) (by norm_num) (sr 2 113593 85195 (by norm_num) (by norm_num) (B 85195 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100975 : Reach 100975 := (sr 1 100975 151463 (by norm_num) (by norm_num) (sr 1 151463 227195 (by norm_num) (by norm_num) (sr 1 227195 340793 (by norm_num) (by norm_num) (sr 2 340793 255595 (by norm_num) (by norm_num) (sr 1 255595 383393 (by norm_num) (by norm_num) (sr 2 383393 287545 (by norm_num) (by norm_num) (sr 2 287545 215659 (by norm_num) (by norm_num) (sr 1 215659 323489 (by norm_num) (by norm_num) (sr 2 323489 242617 (by norm_num) (by norm_num) (sr 2 242617 181963 (by norm_num) (by norm_num) (sr 1 181963 272945 (by norm_num) (by norm_num) (sr 2 272945 204709 (by norm_num) (by norm_num) (sr 4 204709 38383 (by norm_num) (by norm_num) (B 38383 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R100979 : Reach 100979 := (sr 1 100979 151469 (by norm_num) (by norm_num) (sr 3 151469 56801 (by norm_num) (by norm_num) (B 56801 (by norm_num) (by norm_num) (by norm_num))))
theorem R100983 : Reach 100983 := (sr 1 100983 151475 (by norm_num) (by norm_num) (sr 1 151475 227213 (by norm_num) (by norm_num) (sr 3 227213 85205 (by norm_num) (by norm_num) (B 85205 (by norm_num) (by norm_num) (by norm_num)))))
theorem R100987 : Reach 100987 := (sr 1 100987 151481 (by norm_num) (by norm_num) (sr 2 151481 113611 (by norm_num) (by norm_num) (sr 1 113611 170417 (by norm_num) (by norm_num) (sr 2 170417 127813 (by norm_num) (by norm_num) (sr 4 127813 23965 (by norm_num) (by norm_num) (B 23965 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R100991 : Reach 100991 := (sr 1 100991 151487 (by norm_num) (by norm_num) (sr 1 151487 227231 (by norm_num) (by norm_num) (sr 1 227231 340847 (by norm_num) (by norm_num) (sr 1 340847 511271 (by norm_num) (by norm_num) (sr 1 511271 766907 (by norm_num) (by norm_num) (sr 1 766907 1150361 (by norm_num) (by norm_num) (sr 2 1150361 862771 (by norm_num) (by norm_num) (sr 1 862771 1294157 (by norm_num) (by norm_num) (sr 3 1294157 485309 (by norm_num) (by norm_num) (sr 3 485309 181991 (by norm_num) (by norm_num) (sr 1 181991 272987 (by norm_num) (by norm_num) (sr 1 272987 409481 (by norm_num) (by norm_num) (sr 2 409481 307111 (by norm_num) (by norm_num) (sr 1 307111 460667 (by norm_num) (by norm_num) (sr 1 460667 691001 (by norm_num) (by norm_num) (sr 2 691001 518251 (by norm_num) (by norm_num) (sr 1 518251 777377 (by norm_num) (by norm_num) (sr 2 777377 583033 (by norm_num) (by norm_num) (sr 2 583033 437275 (by norm_num) (by norm_num) (sr 1 437275 655913 (by norm_num) (by norm_num) (sr 2 655913 491935 (by norm_num) (by norm_num) (sr 1 491935 737903 (by norm_num) (by norm_num) (sr 1 737903 1106855 (by norm_num) (by norm_num) (sr 1 1106855 1660283 (by norm_num) (by norm_num) (sr 1 1660283 2490425 (by norm_num) (by norm_num) (sr 2 2490425 1867819 (by norm_num) (by norm_num) (sr 1 1867819 2801729 (by norm_num) (by norm_num) (sr 2 2801729 2101297 (by norm_num) (by norm_num) (sr 2 2101297 1575973 (by norm_num) (by norm_num) (sr 4 1575973 295495 (by norm_num) (by norm_num) (sr 1 295495 443243 (by norm_num) (by norm_num) (sr 1 443243 664865 (by norm_num) (by norm_num) (sr 2 664865 498649 (by norm_num) (by norm_num) (sr 2 498649 373987 (by norm_num) (by norm_num) (sr 1 373987 560981 (by norm_num) (by norm_num) (sr 9 560981 3287 (by norm_num) (by norm_num) (B 3287 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))))))))))
theorem R100995 : Reach 100995 := (sr 1 100995 151493 (by norm_num) (by norm_num) (sr 4 151493 28405 (by norm_num) (by norm_num) (B 28405 (by norm_num) (by norm_num) (by norm_num))))
theorem R100999 : Reach 100999 := (sr 1 100999 151499 (by norm_num) (by norm_num) (sr 1 151499 227249 (by norm_num) (by norm_num) (sr 2 227249 170437 (by norm_num) (by norm_num) (sr 4 170437 31957 (by norm_num) (by norm_num) (B 31957 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101003 : Reach 101003 := (sr 1 101003 151505 (by norm_num) (by norm_num) (sr 2 151505 113629 (by norm_num) (by norm_num) (sr 3 113629 42611 (by norm_num) (by norm_num) (B 42611 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101007 : Reach 101007 := (sr 1 101007 151511 (by norm_num) (by norm_num) (sr 1 151511 227267 (by norm_num) (by norm_num) (sr 1 227267 340901 (by norm_num) (by norm_num) (sr 4 340901 63919 (by norm_num) (by norm_num) (B 63919 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101011 : Reach 101011 := (sr 1 101011 151517 (by norm_num) (by norm_num) (sr 3 151517 56819 (by norm_num) (by norm_num) (B 56819 (by norm_num) (by norm_num) (by norm_num))))
theorem R101015 : Reach 101015 := (sr 1 101015 151523 (by norm_num) (by norm_num) (sr 1 151523 227285 (by norm_num) (by norm_num) (sr 7 227285 5327 (by norm_num) (by norm_num) (B 5327 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101019 : Reach 101019 := (sr 1 101019 151529 (by norm_num) (by norm_num) (sr 2 151529 113647 (by norm_num) (by norm_num) (sr 1 113647 170471 (by norm_num) (by norm_num) (sr 1 170471 255707 (by norm_num) (by norm_num) (sr 1 255707 383561 (by norm_num) (by norm_num) (sr 2 383561 287671 (by norm_num) (by norm_num) (sr 1 287671 431507 (by norm_num) (by norm_num) (sr 1 431507 647261 (by norm_num) (by norm_num) (sr 3 647261 242723 (by norm_num) (by norm_num) (sr 1 242723 364085 (by norm_num) (by norm_num) (sr 5 364085 34133 (by norm_num) (by norm_num) (B 34133 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R101023 : Reach 101023 := (sr 1 101023 151535 (by norm_num) (by norm_num) (sr 1 151535 227303 (by norm_num) (by norm_num) (sr 1 227303 340955 (by norm_num) (by norm_num) (sr 1 340955 511433 (by norm_num) (by norm_num) (sr 2 511433 383575 (by norm_num) (by norm_num) (sr 1 383575 575363 (by norm_num) (by norm_num) (sr 1 575363 863045 (by norm_num) (by norm_num) (sr 4 863045 161821 (by norm_num) (by norm_num) (sr 3 161821 60683 (by norm_num) (by norm_num) (B 60683 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R101027 : Reach 101027 := (sr 1 101027 151541 (by norm_num) (by norm_num) (sr 5 151541 14207 (by norm_num) (by norm_num) (B 14207 (by norm_num) (by norm_num) (by norm_num))))
theorem R101031 : Reach 101031 := (sr 1 101031 151547 (by norm_num) (by norm_num) (sr 1 151547 227321 (by norm_num) (by norm_num) (sr 2 227321 170491 (by norm_num) (by norm_num) (sr 1 170491 255737 (by norm_num) (by norm_num) (sr 2 255737 191803 (by norm_num) (by norm_num) (sr 1 191803 287705 (by norm_num) (by norm_num) (sr 2 287705 215779 (by norm_num) (by norm_num) (sr 1 215779 323669 (by norm_num) (by norm_num) (sr 8 323669 3793 (by norm_num) (by norm_num) (B 3793 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R101035 : Reach 101035 := (sr 1 101035 151553 (by norm_num) (by norm_num) (sr 2 151553 113665 (by norm_num) (by norm_num) (sr 2 113665 85249 (by norm_num) (by norm_num) (B 85249 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101039 : Reach 101039 := (sr 1 101039 151559 (by norm_num) (by norm_num) (sr 1 151559 227339 (by norm_num) (by norm_num) (sr 1 227339 341009 (by norm_num) (by norm_num) (sr 2 341009 255757 (by norm_num) (by norm_num) (sr 3 255757 95909 (by norm_num) (by norm_num) (B 95909 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101043 : Reach 101043 := (sr 1 101043 151565 (by norm_num) (by norm_num) (sr 3 151565 56837 (by norm_num) (by norm_num) (B 56837 (by norm_num) (by norm_num) (by norm_num))))
theorem R101047 : Reach 101047 := (sr 1 101047 151571 (by norm_num) (by norm_num) (sr 1 151571 227357 (by norm_num) (by norm_num) (sr 3 227357 85259 (by norm_num) (by norm_num) (B 85259 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101051 : Reach 101051 := (sr 1 101051 151577 (by norm_num) (by norm_num) (sr 2 151577 113683 (by norm_num) (by norm_num) (sr 1 113683 170525 (by norm_num) (by norm_num) (sr 3 170525 63947 (by norm_num) (by norm_num) (B 63947 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101055 : Reach 101055 := (sr 1 101055 151583 (by norm_num) (by norm_num) (sr 1 151583 227375 (by norm_num) (by norm_num) (sr 1 227375 341063 (by norm_num) (by norm_num) (sr 1 341063 511595 (by norm_num) (by norm_num) (sr 1 511595 767393 (by norm_num) (by norm_num) (sr 2 767393 575545 (by norm_num) (by norm_num) (sr 2 575545 431659 (by norm_num) (by norm_num) (sr 1 431659 647489 (by norm_num) (by norm_num) (sr 2 647489 485617 (by norm_num) (by norm_num) (sr 2 485617 364213 (by norm_num) (by norm_num) (sr 5 364213 34145 (by norm_num) (by norm_num) (B 34145 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R101059 : Reach 101059 := (sr 1 101059 151589 (by norm_num) (by norm_num) (sr 4 151589 28423 (by norm_num) (by norm_num) (B 28423 (by norm_num) (by norm_num) (by norm_num))))
theorem R101063 : Reach 101063 := (sr 1 101063 151595 (by norm_num) (by norm_num) (sr 1 151595 227393 (by norm_num) (by norm_num) (sr 2 227393 170545 (by norm_num) (by norm_num) (sr 2 170545 127909 (by norm_num) (by norm_num) (sr 4 127909 23983 (by norm_num) (by norm_num) (B 23983 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101067 : Reach 101067 := (sr 1 101067 151601 (by norm_num) (by norm_num) (sr 2 151601 113701 (by norm_num) (by norm_num) (sr 4 113701 21319 (by norm_num) (by norm_num) (B 21319 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101071 : Reach 101071 := (sr 1 101071 151607 (by norm_num) (by norm_num) (sr 1 151607 227411 (by norm_num) (by norm_num) (sr 1 227411 341117 (by norm_num) (by norm_num) (sr 3 341117 127919 (by norm_num) (by norm_num) (sr 1 127919 191879 (by norm_num) (by norm_num) (sr 1 191879 287819 (by norm_num) (by norm_num) (sr 1 287819 431729 (by norm_num) (by norm_num) (sr 2 431729 323797 (by norm_num) (by norm_num) (sr 7 323797 7589 (by norm_num) (by norm_num) (B 7589 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R101075 : Reach 101075 := (sr 1 101075 151613 (by norm_num) (by norm_num) (sr 3 151613 56855 (by norm_num) (by norm_num) (B 56855 (by norm_num) (by norm_num) (by norm_num))))
theorem R101079 : Reach 101079 := (sr 1 101079 151619 (by norm_num) (by norm_num) (sr 1 151619 227429 (by norm_num) (by norm_num) (sr 4 227429 42643 (by norm_num) (by norm_num) (B 42643 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101083 : Reach 101083 := (sr 1 101083 151625 (by norm_num) (by norm_num) (sr 2 151625 113719 (by norm_num) (by norm_num) (sr 1 113719 170579 (by norm_num) (by norm_num) (sr 1 170579 255869 (by norm_num) (by norm_num) (sr 3 255869 95951 (by norm_num) (by norm_num) (B 95951 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101087 : Reach 101087 := (sr 1 101087 151631 (by norm_num) (by norm_num) (sr 1 151631 227447 (by norm_num) (by norm_num) (sr 1 227447 341171 (by norm_num) (by norm_num) (sr 1 341171 511757 (by norm_num) (by norm_num) (sr 3 511757 191909 (by norm_num) (by norm_num) (sr 4 191909 35983 (by norm_num) (by norm_num) (B 35983 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R101091 : Reach 101091 := (sr 1 101091 151637 (by norm_num) (by norm_num) (sr 8 151637 1777 (by norm_num) (by norm_num) (B 1777 (by norm_num) (by norm_num) (by norm_num))))
theorem R101095 : Reach 101095 := (sr 1 101095 151643 (by norm_num) (by norm_num) (sr 1 151643 227465 (by norm_num) (by norm_num) (sr 2 227465 170599 (by norm_num) (by norm_num) (sr 1 170599 255899 (by norm_num) (by norm_num) (sr 1 255899 383849 (by norm_num) (by norm_num) (sr 2 383849 287887 (by norm_num) (by norm_num) (sr 1 287887 431831 (by norm_num) (by norm_num) (sr 1 431831 647747 (by norm_num) (by norm_num) (sr 1 647747 971621 (by norm_num) (by norm_num) (sr 4 971621 182179 (by norm_num) (by norm_num) (sr 1 182179 273269 (by norm_num) (by norm_num) (sr 5 273269 25619 (by norm_num) (by norm_num) (B 25619 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R101099 : Reach 101099 := (sr 1 101099 151649 (by norm_num) (by norm_num) (sr 2 151649 113737 (by norm_num) (by norm_num) (sr 2 113737 85303 (by norm_num) (by norm_num) (B 85303 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101103 : Reach 101103 := (sr 1 101103 151655 (by norm_num) (by norm_num) (sr 1 151655 227483 (by norm_num) (by norm_num) (sr 1 227483 341225 (by norm_num) (by norm_num) (sr 2 341225 255919 (by norm_num) (by norm_num) (sr 1 255919 383879 (by norm_num) (by norm_num) (sr 1 383879 575819 (by norm_num) (by norm_num) (sr 1 575819 863729 (by norm_num) (by norm_num) (sr 2 863729 647797 (by norm_num) (by norm_num) (sr 5 647797 60731 (by norm_num) (by norm_num) (B 60731 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R101107 : Reach 101107 := (sr 1 101107 151661 (by norm_num) (by norm_num) (sr 3 151661 56873 (by norm_num) (by norm_num) (B 56873 (by norm_num) (by norm_num) (by norm_num))))
theorem R101111 : Reach 101111 := (sr 1 101111 151667 (by norm_num) (by norm_num) (sr 1 151667 227501 (by norm_num) (by norm_num) (sr 3 227501 85313 (by norm_num) (by norm_num) (B 85313 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101115 : Reach 101115 := (sr 1 101115 151673 (by norm_num) (by norm_num) (sr 2 151673 113755 (by norm_num) (by norm_num) (sr 1 113755 170633 (by norm_num) (by norm_num) (sr 2 170633 127975 (by norm_num) (by norm_num) (sr 1 127975 191963 (by norm_num) (by norm_num) (sr 1 191963 287945 (by norm_num) (by norm_num) (sr 2 287945 215959 (by norm_num) (by norm_num) (sr 1 215959 323939 (by norm_num) (by norm_num) (sr 1 323939 485909 (by norm_num) (by norm_num) (sr 6 485909 22777 (by norm_num) (by norm_num) (B 22777 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R101119 : Reach 101119 := (sr 1 101119 151679 (by norm_num) (by norm_num) (sr 1 151679 227519 (by norm_num) (by norm_num) (sr 1 227519 341279 (by norm_num) (by norm_num) (sr 1 341279 511919 (by norm_num) (by norm_num) (sr 1 511919 767879 (by norm_num) (by norm_num) (sr 1 767879 1151819 (by norm_num) (by norm_num) (sr 1 1151819 1727729 (by norm_num) (by norm_num) (sr 2 1727729 1295797 (by norm_num) (by norm_num) (sr 5 1295797 121481 (by norm_num) (by norm_num) (sr 2 121481 91111 (by norm_num) (by norm_num) (B 91111 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R101123 : Reach 101123 := (sr 1 101123 151685 (by norm_num) (by norm_num) (sr 4 151685 28441 (by norm_num) (by norm_num) (B 28441 (by norm_num) (by norm_num) (by norm_num))))
theorem R101127 : Reach 101127 := (sr 1 101127 151691 (by norm_num) (by norm_num) (sr 1 151691 227537 (by norm_num) (by norm_num) (sr 2 227537 170653 (by norm_num) (by norm_num) (sr 3 170653 63995 (by norm_num) (by norm_num) (B 63995 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101131 : Reach 101131 := (sr 1 101131 151697 (by norm_num) (by norm_num) (sr 2 151697 113773 (by norm_num) (by norm_num) (sr 3 113773 42665 (by norm_num) (by norm_num) (B 42665 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101135 : Reach 101135 := (sr 1 101135 151703 (by norm_num) (by norm_num) (sr 1 151703 227555 (by norm_num) (by norm_num) (sr 1 227555 341333 (by norm_num) (by norm_num) (sr 13 341333 125 (by norm_num) (by norm_num) (B 125 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101139 : Reach 101139 := (sr 1 101139 151709 (by norm_num) (by norm_num) (sr 3 151709 56891 (by norm_num) (by norm_num) (B 56891 (by norm_num) (by norm_num) (by norm_num))))
theorem R101143 : Reach 101143 := (sr 1 101143 151715 (by norm_num) (by norm_num) (sr 1 151715 227573 (by norm_num) (by norm_num) (sr 5 227573 21335 (by norm_num) (by norm_num) (B 21335 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101147 : Reach 101147 := (sr 1 101147 151721 (by norm_num) (by norm_num) (sr 2 151721 113791 (by norm_num) (by norm_num) (sr 1 113791 170687 (by norm_num) (by norm_num) (sr 1 170687 256031 (by norm_num) (by norm_num) (sr 1 256031 384047 (by norm_num) (by norm_num) (sr 1 384047 576071 (by norm_num) (by norm_num) (sr 1 576071 864107 (by norm_num) (by norm_num) (sr 1 864107 1296161 (by norm_num) (by norm_num) (sr 2 1296161 972121 (by norm_num) (by norm_num) (sr 2 972121 729091 (by norm_num) (by norm_num) (sr 1 729091 1093637 (by norm_num) (by norm_num) (sr 4 1093637 205057 (by norm_num) (by norm_num) (sr 2 205057 153793 (by norm_num) (by norm_num) (sr 2 153793 115345 (by norm_num) (by norm_num) (sr 2 115345 86509 (by norm_num) (by norm_num) (B 86509 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R101151 : Reach 101151 := (sr 1 101151 151727 (by norm_num) (by norm_num) (sr 1 151727 227591 (by norm_num) (by norm_num) (sr 1 227591 341387 (by norm_num) (by norm_num) (sr 1 341387 512081 (by norm_num) (by norm_num) (sr 2 512081 384061 (by norm_num) (by norm_num) (sr 3 384061 144023 (by norm_num) (by norm_num) (sr 1 144023 216035 (by norm_num) (by norm_num) (sr 1 216035 324053 (by norm_num) (by norm_num) (sr 7 324053 7595 (by norm_num) (by norm_num) (B 7595 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R101155 : Reach 101155 := (sr 1 101155 151733 (by norm_num) (by norm_num) (sr 5 151733 14225 (by norm_num) (by norm_num) (B 14225 (by norm_num) (by norm_num) (by norm_num))))
theorem R101159 : Reach 101159 := (sr 1 101159 151739 (by norm_num) (by norm_num) (sr 1 151739 227609 (by norm_num) (by norm_num) (sr 2 227609 170707 (by norm_num) (by norm_num) (sr 1 170707 256061 (by norm_num) (by norm_num) (sr 3 256061 96023 (by norm_num) (by norm_num) (B 96023 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101163 : Reach 101163 := (sr 1 101163 151745 (by norm_num) (by norm_num) (sr 2 151745 113809 (by norm_num) (by norm_num) (sr 2 113809 85357 (by norm_num) (by norm_num) (B 85357 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101167 : Reach 101167 := (sr 1 101167 151751 (by norm_num) (by norm_num) (sr 1 151751 227627 (by norm_num) (by norm_num) (sr 1 227627 341441 (by norm_num) (by norm_num) (sr 2 341441 256081 (by norm_num) (by norm_num) (sr 2 256081 192061 (by norm_num) (by norm_num) (sr 3 192061 72023 (by norm_num) (by norm_num) (B 72023 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R101171 : Reach 101171 := (sr 1 101171 151757 (by norm_num) (by norm_num) (sr 3 151757 56909 (by norm_num) (by norm_num) (B 56909 (by norm_num) (by norm_num) (by norm_num))))
theorem R101175 : Reach 101175 := (sr 1 101175 151763 (by norm_num) (by norm_num) (sr 1 151763 227645 (by norm_num) (by norm_num) (sr 3 227645 85367 (by norm_num) (by norm_num) (B 85367 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101179 : Reach 101179 := (sr 1 101179 151769 (by norm_num) (by norm_num) (sr 2 151769 113827 (by norm_num) (by norm_num) (sr 1 113827 170741 (by norm_num) (by norm_num) (sr 5 170741 16007 (by norm_num) (by norm_num) (B 16007 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101183 : Reach 101183 := (sr 1 101183 151775 (by norm_num) (by norm_num) (sr 1 151775 227663 (by norm_num) (by norm_num) (sr 1 227663 341495 (by norm_num) (by norm_num) (sr 1 341495 512243 (by norm_num) (by norm_num) (sr 1 512243 768365 (by norm_num) (by norm_num) (sr 3 768365 288137 (by norm_num) (by norm_num) (sr 2 288137 216103 (by norm_num) (by norm_num) (sr 1 216103 324155 (by norm_num) (by norm_num) (sr 1 324155 486233 (by norm_num) (by norm_num) (sr 2 486233 364675 (by norm_num) (by norm_num) (sr 1 364675 547013 (by norm_num) (by norm_num) (sr 4 547013 102565 (by norm_num) (by norm_num) (sr 4 102565 19231 (by norm_num) (by norm_num) (B 19231 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R101187 : Reach 101187 := (sr 1 101187 151781 (by norm_num) (by norm_num) (sr 4 151781 28459 (by norm_num) (by norm_num) (B 28459 (by norm_num) (by norm_num) (by norm_num))))
theorem R101191 : Reach 101191 := (sr 1 101191 151787 (by norm_num) (by norm_num) (sr 1 151787 227681 (by norm_num) (by norm_num) (sr 2 227681 170761 (by norm_num) (by norm_num) (sr 2 170761 128071 (by norm_num) (by norm_num) (sr 1 128071 192107 (by norm_num) (by norm_num) (sr 1 192107 288161 (by norm_num) (by norm_num) (sr 2 288161 216121 (by norm_num) (by norm_num) (sr 2 216121 162091 (by norm_num) (by norm_num) (sr 1 162091 243137 (by norm_num) (by norm_num) (sr 2 243137 182353 (by norm_num) (by norm_num) (sr 2 182353 136765 (by norm_num) (by norm_num) (sr 3 136765 51287 (by norm_num) (by norm_num) (B 51287 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R101195 : Reach 101195 := (sr 1 101195 151793 (by norm_num) (by norm_num) (sr 2 151793 113845 (by norm_num) (by norm_num) (sr 5 113845 10673 (by norm_num) (by norm_num) (B 10673 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101199 : Reach 101199 := (sr 1 101199 151799 (by norm_num) (by norm_num) (sr 1 151799 227699 (by norm_num) (by norm_num) (sr 1 227699 341549 (by norm_num) (by norm_num) (sr 3 341549 128081 (by norm_num) (by norm_num) (sr 2 128081 96061 (by norm_num) (by norm_num) (B 96061 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101203 : Reach 101203 := (sr 1 101203 151805 (by norm_num) (by norm_num) (sr 3 151805 56927 (by norm_num) (by norm_num) (B 56927 (by norm_num) (by norm_num) (by norm_num))))
theorem R101207 : Reach 101207 := (sr 1 101207 151811 (by norm_num) (by norm_num) (sr 1 151811 227717 (by norm_num) (by norm_num) (sr 4 227717 42697 (by norm_num) (by norm_num) (B 42697 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101211 : Reach 101211 := (sr 1 101211 151817 (by norm_num) (by norm_num) (sr 2 151817 113863 (by norm_num) (by norm_num) (sr 1 113863 170795 (by norm_num) (by norm_num) (sr 1 170795 256193 (by norm_num) (by norm_num) (sr 2 256193 192145 (by norm_num) (by norm_num) (sr 2 192145 144109 (by norm_num) (by norm_num) (sr 3 144109 54041 (by norm_num) (by norm_num) (B 54041 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R101215 : Reach 101215 := (sr 1 101215 151823 (by norm_num) (by norm_num) (sr 1 151823 227735 (by norm_num) (by norm_num) (sr 1 227735 341603 (by norm_num) (by norm_num) (sr 1 341603 512405 (by norm_num) (by norm_num) (sr 6 512405 24019 (by norm_num) (by norm_num) (B 24019 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101219 : Reach 101219 := (sr 1 101219 151829 (by norm_num) (by norm_num) (sr 6 151829 7117 (by norm_num) (by norm_num) (B 7117 (by norm_num) (by norm_num) (by norm_num))))
theorem R101223 : Reach 101223 := (sr 1 101223 151835 (by norm_num) (by norm_num) (sr 1 151835 227753 (by norm_num) (by norm_num) (sr 2 227753 170815 (by norm_num) (by norm_num) (sr 1 170815 256223 (by norm_num) (by norm_num) (sr 1 256223 384335 (by norm_num) (by norm_num) (sr 1 384335 576503 (by norm_num) (by norm_num) (sr 1 576503 864755 (by norm_num) (by norm_num) (sr 1 864755 1297133 (by norm_num) (by norm_num) (sr 3 1297133 486425 (by norm_num) (by norm_num) (sr 2 486425 364819 (by norm_num) (by norm_num) (sr 1 364819 547229 (by norm_num) (by norm_num) (sr 3 547229 205211 (by norm_num) (by norm_num) (sr 1 205211 307817 (by norm_num) (by norm_num) (sr 2 307817 230863 (by norm_num) (by norm_num) (sr 1 230863 346295 (by norm_num) (by norm_num) (sr 1 346295 519443 (by norm_num) (by norm_num) (sr 1 519443 779165 (by norm_num) (by norm_num) (sr 3 779165 292187 (by norm_num) (by norm_num) (sr 1 292187 438281 (by norm_num) (by norm_num) (sr 2 438281 328711 (by norm_num) (by norm_num) (sr 1 328711 493067 (by norm_num) (by norm_num) (sr 1 493067 739601 (by norm_num) (by norm_num) (sr 2 739601 554701 (by norm_num) (by norm_num) (sr 3 554701 208013 (by norm_num) (by norm_num) (sr 3 208013 78005 (by norm_num) (by norm_num) (B 78005 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))
theorem R101227 : Reach 101227 := (sr 1 101227 151841 (by norm_num) (by norm_num) (sr 2 151841 113881 (by norm_num) (by norm_num) (sr 2 113881 85411 (by norm_num) (by norm_num) (B 85411 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101231 : Reach 101231 := (sr 1 101231 151847 (by norm_num) (by norm_num) (sr 1 151847 227771 (by norm_num) (by norm_num) (sr 1 227771 341657 (by norm_num) (by norm_num) (sr 2 341657 256243 (by norm_num) (by norm_num) (sr 1 256243 384365 (by norm_num) (by norm_num) (sr 3 384365 144137 (by norm_num) (by norm_num) (sr 2 144137 108103 (by norm_num) (by norm_num) (sr 1 108103 162155 (by norm_num) (by norm_num) (sr 1 162155 243233 (by norm_num) (by norm_num) (sr 2 243233 182425 (by norm_num) (by norm_num) (sr 2 182425 136819 (by norm_num) (by norm_num) (sr 1 136819 205229 (by norm_num) (by norm_num) (sr 3 205229 76961 (by norm_num) (by norm_num) (B 76961 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R101235 : Reach 101235 := (sr 1 101235 151853 (by norm_num) (by norm_num) (sr 3 151853 56945 (by norm_num) (by norm_num) (B 56945 (by norm_num) (by norm_num) (by norm_num))))
theorem R101239 : Reach 101239 := (sr 1 101239 151859 (by norm_num) (by norm_num) (sr 1 151859 227789 (by norm_num) (by norm_num) (sr 3 227789 85421 (by norm_num) (by norm_num) (B 85421 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101243 : Reach 101243 := (sr 1 101243 151865 (by norm_num) (by norm_num) (sr 2 151865 113899 (by norm_num) (by norm_num) (sr 1 113899 170849 (by norm_num) (by norm_num) (sr 2 170849 128137 (by norm_num) (by norm_num) (sr 2 128137 96103 (by norm_num) (by norm_num) (B 96103 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101247 : Reach 101247 := (sr 1 101247 151871 (by norm_num) (by norm_num) (sr 1 151871 227807 (by norm_num) (by norm_num) (sr 1 227807 341711 (by norm_num) (by norm_num) (sr 1 341711 512567 (by norm_num) (by norm_num) (sr 1 512567 768851 (by norm_num) (by norm_num) (sr 1 768851 1153277 (by norm_num) (by norm_num) (sr 3 1153277 432479 (by norm_num) (by norm_num) (sr 1 432479 648719 (by norm_num) (by norm_num) (sr 1 648719 973079 (by norm_num) (by norm_num) (sr 1 973079 1459619 (by norm_num) (by norm_num) (sr 1 1459619 2189429 (by norm_num) (by norm_num) (sr 5 2189429 205259 (by norm_num) (by norm_num) (sr 1 205259 307889 (by norm_num) (by norm_num) (sr 2 307889 230917 (by norm_num) (by norm_num) (sr 4 230917 43297 (by norm_num) (by norm_num) (B 43297 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R101251 : Reach 101251 := (sr 1 101251 151877 (by norm_num) (by norm_num) (sr 4 151877 28477 (by norm_num) (by norm_num) (B 28477 (by norm_num) (by norm_num) (by norm_num))))
theorem R101255 : Reach 101255 := (sr 1 101255 151883 (by norm_num) (by norm_num) (sr 1 151883 227825 (by norm_num) (by norm_num) (sr 2 227825 170869 (by norm_num) (by norm_num) (sr 5 170869 16019 (by norm_num) (by norm_num) (B 16019 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101259 : Reach 101259 := (sr 1 101259 151889 (by norm_num) (by norm_num) (sr 2 151889 113917 (by norm_num) (by norm_num) (sr 3 113917 42719 (by norm_num) (by norm_num) (B 42719 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101263 : Reach 101263 := (sr 1 101263 151895 (by norm_num) (by norm_num) (sr 1 151895 227843 (by norm_num) (by norm_num) (sr 1 227843 341765 (by norm_num) (by norm_num) (sr 4 341765 64081 (by norm_num) (by norm_num) (B 64081 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101267 : Reach 101267 := (sr 1 101267 151901 (by norm_num) (by norm_num) (sr 3 151901 56963 (by norm_num) (by norm_num) (B 56963 (by norm_num) (by norm_num) (by norm_num))))
theorem R101271 : Reach 101271 := (sr 1 101271 151907 (by norm_num) (by norm_num) (sr 1 151907 227861 (by norm_num) (by norm_num) (sr 6 227861 10681 (by norm_num) (by norm_num) (B 10681 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101275 : Reach 101275 := (sr 1 101275 151913 (by norm_num) (by norm_num) (sr 2 151913 113935 (by norm_num) (by norm_num) (sr 1 113935 170903 (by norm_num) (by norm_num) (sr 1 170903 256355 (by norm_num) (by norm_num) (sr 1 256355 384533 (by norm_num) (by norm_num) (sr 6 384533 18025 (by norm_num) (by norm_num) (B 18025 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R101279 : Reach 101279 := (sr 1 101279 151919 (by norm_num) (by norm_num) (sr 1 151919 227879 (by norm_num) (by norm_num) (sr 1 227879 341819 (by norm_num) (by norm_num) (sr 1 341819 512729 (by norm_num) (by norm_num) (sr 2 512729 384547 (by norm_num) (by norm_num) (sr 1 384547 576821 (by norm_num) (by norm_num) (sr 5 576821 54077 (by norm_num) (by norm_num) (B 54077 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R101283 : Reach 101283 := (sr 1 101283 151925 (by norm_num) (by norm_num) (sr 5 151925 14243 (by norm_num) (by norm_num) (B 14243 (by norm_num) (by norm_num) (by norm_num))))
theorem R101287 : Reach 101287 := (sr 1 101287 151931 (by norm_num) (by norm_num) (sr 1 151931 227897 (by norm_num) (by norm_num) (sr 2 227897 170923 (by norm_num) (by norm_num) (sr 1 170923 256385 (by norm_num) (by norm_num) (sr 2 256385 192289 (by norm_num) (by norm_num) (sr 2 192289 144217 (by norm_num) (by norm_num) (sr 2 144217 108163 (by norm_num) (by norm_num) (sr 1 108163 162245 (by norm_num) (by norm_num) (sr 4 162245 30421 (by norm_num) (by norm_num) (B 30421 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R101291 : Reach 101291 := (sr 1 101291 151937 (by norm_num) (by norm_num) (sr 2 151937 113953 (by norm_num) (by norm_num) (sr 2 113953 85465 (by norm_num) (by norm_num) (B 85465 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101295 : Reach 101295 := (sr 1 101295 151943 (by norm_num) (by norm_num) (sr 1 151943 227915 (by norm_num) (by norm_num) (sr 1 227915 341873 (by norm_num) (by norm_num) (sr 2 341873 256405 (by norm_num) (by norm_num) (sr 6 256405 12019 (by norm_num) (by norm_num) (B 12019 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101299 : Reach 101299 := (sr 1 101299 151949 (by norm_num) (by norm_num) (sr 3 151949 56981 (by norm_num) (by norm_num) (B 56981 (by norm_num) (by norm_num) (by norm_num))))
theorem R101303 : Reach 101303 := (sr 1 101303 151955 (by norm_num) (by norm_num) (sr 1 151955 227933 (by norm_num) (by norm_num) (sr 3 227933 85475 (by norm_num) (by norm_num) (B 85475 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101307 : Reach 101307 := (sr 1 101307 151961 (by norm_num) (by norm_num) (sr 2 151961 113971 (by norm_num) (by norm_num) (sr 1 113971 170957 (by norm_num) (by norm_num) (sr 3 170957 64109 (by norm_num) (by norm_num) (B 64109 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101311 : Reach 101311 := (sr 1 101311 151967 (by norm_num) (by norm_num) (sr 1 151967 227951 (by norm_num) (by norm_num) (sr 1 227951 341927 (by norm_num) (by norm_num) (sr 1 341927 512891 (by norm_num) (by norm_num) (sr 1 512891 769337 (by norm_num) (by norm_num) (sr 2 769337 577003 (by norm_num) (by norm_num) (sr 1 577003 865505 (by norm_num) (by norm_num) (sr 2 865505 649129 (by norm_num) (by norm_num) (sr 2 649129 486847 (by norm_num) (by norm_num) (sr 1 486847 730271 (by norm_num) (by norm_num) (sr 1 730271 1095407 (by norm_num) (by norm_num) (sr 1 1095407 1643111 (by norm_num) (by norm_num) (sr 1 1643111 2464667 (by norm_num) (by norm_num) (sr 1 2464667 3697001 (by norm_num) (by norm_num) (sr 2 3697001 2772751 (by norm_num) (by norm_num) (sr 1 2772751 4159127 (by norm_num) (by norm_num) (sr 1 4159127 6238691 (by norm_num) (by norm_num) (sr 1 6238691 9358037 (by norm_num) (by norm_num) (sr 7 9358037 219329 (by norm_num) (by norm_num) (sr 2 219329 164497 (by norm_num) (by norm_num) (sr 2 164497 123373 (by norm_num) (by norm_num) (sr 3 123373 46265 (by norm_num) (by norm_num) (B 46265 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R101315 : Reach 101315 := (sr 1 101315 151973 (by norm_num) (by norm_num) (sr 4 151973 28495 (by norm_num) (by norm_num) (B 28495 (by norm_num) (by norm_num) (by norm_num))))
theorem R101319 : Reach 101319 := (sr 1 101319 151979 (by norm_num) (by norm_num) (sr 1 151979 227969 (by norm_num) (by norm_num) (sr 2 227969 170977 (by norm_num) (by norm_num) (sr 2 170977 128233 (by norm_num) (by norm_num) (sr 2 128233 96175 (by norm_num) (by norm_num) (B 96175 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101323 : Reach 101323 := (sr 1 101323 151985 (by norm_num) (by norm_num) (sr 2 151985 113989 (by norm_num) (by norm_num) (sr 4 113989 21373 (by norm_num) (by norm_num) (B 21373 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101327 : Reach 101327 := (sr 1 101327 151991 (by norm_num) (by norm_num) (sr 1 151991 227987 (by norm_num) (by norm_num) (sr 1 227987 341981 (by norm_num) (by norm_num) (sr 3 341981 128243 (by norm_num) (by norm_num) (sr 1 128243 192365 (by norm_num) (by norm_num) (sr 3 192365 72137 (by norm_num) (by norm_num) (B 72137 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R101331 : Reach 101331 := (sr 1 101331 151997 (by norm_num) (by norm_num) (sr 3 151997 56999 (by norm_num) (by norm_num) (B 56999 (by norm_num) (by norm_num) (by norm_num))))
theorem R101335 : Reach 101335 := (sr 1 101335 152003 (by norm_num) (by norm_num) (sr 1 152003 228005 (by norm_num) (by norm_num) (sr 4 228005 42751 (by norm_num) (by norm_num) (B 42751 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101339 : Reach 101339 := (sr 1 101339 152009 (by norm_num) (by norm_num) (sr 2 152009 114007 (by norm_num) (by norm_num) (sr 1 114007 171011 (by norm_num) (by norm_num) (sr 1 171011 256517 (by norm_num) (by norm_num) (sr 4 256517 48097 (by norm_num) (by norm_num) (B 48097 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101343 : Reach 101343 := (sr 1 101343 152015 (by norm_num) (by norm_num) (sr 1 152015 228023 (by norm_num) (by norm_num) (sr 1 228023 342035 (by norm_num) (by norm_num) (sr 1 342035 513053 (by norm_num) (by norm_num) (sr 3 513053 192395 (by norm_num) (by norm_num) (sr 1 192395 288593 (by norm_num) (by norm_num) (sr 2 288593 216445 (by norm_num) (by norm_num) (sr 3 216445 81167 (by norm_num) (by norm_num) (B 81167 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R101347 : Reach 101347 := (sr 1 101347 152021 (by norm_num) (by norm_num) (sr 7 152021 3563 (by norm_num) (by norm_num) (B 3563 (by norm_num) (by norm_num) (by norm_num))))
theorem R101351 : Reach 101351 := (sr 1 101351 152027 (by norm_num) (by norm_num) (sr 1 152027 228041 (by norm_num) (by norm_num) (sr 2 228041 171031 (by norm_num) (by norm_num) (sr 1 171031 256547 (by norm_num) (by norm_num) (sr 1 256547 384821 (by norm_num) (by norm_num) (sr 5 384821 36077 (by norm_num) (by norm_num) (B 36077 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R101355 : Reach 101355 := (sr 1 101355 152033 (by norm_num) (by norm_num) (sr 2 152033 114025 (by norm_num) (by norm_num) (sr 2 114025 85519 (by norm_num) (by norm_num) (B 85519 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101359 : Reach 101359 := (sr 1 101359 152039 (by norm_num) (by norm_num) (sr 1 152039 228059 (by norm_num) (by norm_num) (sr 1 228059 342089 (by norm_num) (by norm_num) (sr 2 342089 256567 (by norm_num) (by norm_num) (sr 1 256567 384851 (by norm_num) (by norm_num) (sr 1 384851 577277 (by norm_num) (by norm_num) (sr 3 577277 216479 (by norm_num) (by norm_num) (sr 1 216479 324719 (by norm_num) (by norm_num) (sr 1 324719 487079 (by norm_num) (by norm_num) (sr 1 487079 730619 (by norm_num) (by norm_num) (sr 1 730619 1095929 (by norm_num) (by norm_num) (sr 2 1095929 821947 (by norm_num) (by norm_num) (sr 1 821947 1232921 (by norm_num) (by norm_num) (sr 2 1232921 924691 (by norm_num) (by norm_num) (sr 1 924691 1387037 (by norm_num) (by norm_num) (sr 3 1387037 520139 (by norm_num) (by norm_num) (sr 1 520139 780209 (by norm_num) (by norm_num) (sr 2 780209 585157 (by norm_num) (by norm_num) (sr 4 585157 109717 (by norm_num) (by norm_num) (sr 6 109717 5143 (by norm_num) (by norm_num) (B 5143 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))
theorem R101363 : Reach 101363 := (sr 1 101363 152045 (by norm_num) (by norm_num) (sr 3 152045 57017 (by norm_num) (by norm_num) (B 57017 (by norm_num) (by norm_num) (by norm_num))))
theorem R101367 : Reach 101367 := (sr 1 101367 152051 (by norm_num) (by norm_num) (sr 1 152051 228077 (by norm_num) (by norm_num) (sr 3 228077 85529 (by norm_num) (by norm_num) (B 85529 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101371 : Reach 101371 := (sr 1 101371 152057 (by norm_num) (by norm_num) (sr 2 152057 114043 (by norm_num) (by norm_num) (sr 1 114043 171065 (by norm_num) (by norm_num) (sr 2 171065 128299 (by norm_num) (by norm_num) (sr 1 128299 192449 (by norm_num) (by norm_num) (sr 2 192449 144337 (by norm_num) (by norm_num) (sr 2 144337 108253 (by norm_num) (by norm_num) (sr 3 108253 40595 (by norm_num) (by norm_num) (B 40595 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R101375 : Reach 101375 := (sr 1 101375 152063 (by norm_num) (by norm_num) (sr 1 152063 228095 (by norm_num) (by norm_num) (sr 1 228095 342143 (by norm_num) (by norm_num) (sr 1 342143 513215 (by norm_num) (by norm_num) (sr 1 513215 769823 (by norm_num) (by norm_num) (sr 1 769823 1154735 (by norm_num) (by norm_num) (sr 1 1154735 1732103 (by norm_num) (by norm_num) (sr 1 1732103 2598155 (by norm_num) (by norm_num) (sr 1 2598155 3897233 (by norm_num) (by norm_num) (sr 2 3897233 2922925 (by norm_num) (by norm_num) (sr 3 2922925 1096097 (by norm_num) (by norm_num) (sr 2 1096097 822073 (by norm_num) (by norm_num) (sr 2 822073 616555 (by norm_num) (by norm_num) (sr 1 616555 924833 (by norm_num) (by norm_num) (sr 2 924833 693625 (by norm_num) (by norm_num) (sr 2 693625 520219 (by norm_num) (by norm_num) (sr 1 520219 780329 (by norm_num) (by norm_num) (sr 2 780329 585247 (by norm_num) (by norm_num) (sr 1 585247 877871 (by norm_num) (by norm_num) (sr 1 877871 1316807 (by norm_num) (by norm_num) (sr 1 1316807 1975211 (by norm_num) (by norm_num) (sr 1 1975211 2962817 (by norm_num) (by norm_num) (sr 2 2962817 2222113 (by norm_num) (by norm_num) (sr 2 2222113 1666585 (by norm_num) (by norm_num) (sr 2 1666585 1249939 (by norm_num) (by norm_num) (sr 1 1249939 1874909 (by norm_num) (by norm_num) (sr 3 1874909 703091 (by norm_num) (by norm_num) (sr 1 703091 1054637 (by norm_num) (by norm_num) (sr 3 1054637 395489 (by norm_num) (by norm_num) (sr 2 395489 296617 (by norm_num) (by norm_num) (sr 2 296617 222463 (by norm_num) (by norm_num) (sr 1 222463 333695 (by norm_num) (by norm_num) (sr 1 333695 500543 (by norm_num) (by norm_num) (sr 1 500543 750815 (by norm_num) (by norm_num) (sr 1 750815 1126223 (by norm_num) (by norm_num) (sr 1 1126223 1689335 (by norm_num) (by norm_num) (sr 1 1689335 2534003 (by norm_num) (by norm_num) (sr 1 2534003 3801005 (by norm_num) (by norm_num) (sr 3 3801005 1425377 (by norm_num) (by norm_num) (sr 2 1425377 1069033 (by norm_num) (by norm_num) (sr 2 1069033 801775 (by norm_num) (by norm_num) (sr 1 801775 1202663 (by norm_num) (by norm_num) (sr 1 1202663 1803995 (by norm_num) (by norm_num) (sr 1 1803995 2705993 (by norm_num) (by norm_num) (sr 2 2705993 2029495 (by norm_num) (by norm_num) (sr 1 2029495 3044243 (by norm_num) (by norm_num) (sr 1 3044243 4566365 (by norm_num) (by norm_num) (sr 3 4566365 1712387 (by norm_num) (by norm_num) (sr 1 1712387 2568581 (by norm_num) (by norm_num) (sr 4 2568581 481609 (by norm_num) (by norm_num) (sr 2 481609 361207 (by norm_num) (by norm_num) (sr 1 361207 541811 (by norm_num) (by norm_num) (sr 1 541811 812717 (by norm_num) (by norm_num) (sr 3 812717 304769 (by norm_num) (by norm_num) (sr 2 304769 228577 (by norm_num) (by norm_num) (sr 2 228577 171433 (by norm_num) (by norm_num) (sr 2 171433 128575 (by norm_num) (by norm_num) (sr 1 128575 192863 (by norm_num) (by norm_num) (sr 1 192863 289295 (by norm_num) (by norm_num) (sr 1 289295 433943 (by norm_num) (by norm_num) (sr 1 433943 650915 (by norm_num) (by norm_num) (sr 1 650915 976373 (by norm_num) (by norm_num) (sr 5 976373 91535 (by norm_num) (by norm_num) (B 91535 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem R101379 : Reach 101379 := (sr 1 101379 152069 (by norm_num) (by norm_num) (sr 4 152069 28513 (by norm_num) (by norm_num) (B 28513 (by norm_num) (by norm_num) (by norm_num))))
theorem R101383 : Reach 101383 := (sr 1 101383 152075 (by norm_num) (by norm_num) (sr 1 152075 228113 (by norm_num) (by norm_num) (sr 2 228113 171085 (by norm_num) (by norm_num) (sr 3 171085 64157 (by norm_num) (by norm_num) (B 64157 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101387 : Reach 101387 := (sr 1 101387 152081 (by norm_num) (by norm_num) (sr 2 152081 114061 (by norm_num) (by norm_num) (sr 3 114061 42773 (by norm_num) (by norm_num) (B 42773 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101391 : Reach 101391 := (sr 1 101391 152087 (by norm_num) (by norm_num) (sr 1 152087 228131 (by norm_num) (by norm_num) (sr 1 228131 342197 (by norm_num) (by norm_num) (sr 5 342197 32081 (by norm_num) (by norm_num) (B 32081 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101395 : Reach 101395 := (sr 1 101395 152093 (by norm_num) (by norm_num) (sr 3 152093 57035 (by norm_num) (by norm_num) (B 57035 (by norm_num) (by norm_num) (by norm_num))))
theorem R101399 : Reach 101399 := (sr 1 101399 152099 (by norm_num) (by norm_num) (sr 1 152099 228149 (by norm_num) (by norm_num) (sr 5 228149 21389 (by norm_num) (by norm_num) (B 21389 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101403 : Reach 101403 := (sr 1 101403 152105 (by norm_num) (by norm_num) (sr 2 152105 114079 (by norm_num) (by norm_num) (sr 1 114079 171119 (by norm_num) (by norm_num) (sr 1 171119 256679 (by norm_num) (by norm_num) (sr 1 256679 385019 (by norm_num) (by norm_num) (sr 1 385019 577529 (by norm_num) (by norm_num) (sr 2 577529 433147 (by norm_num) (by norm_num) (sr 1 433147 649721 (by norm_num) (by norm_num) (sr 2 649721 487291 (by norm_num) (by norm_num) (sr 1 487291 730937 (by norm_num) (by norm_num) (sr 2 730937 548203 (by norm_num) (by norm_num) (sr 1 548203 822305 (by norm_num) (by norm_num) (sr 2 822305 616729 (by norm_num) (by norm_num) (sr 2 616729 462547 (by norm_num) (by norm_num) (sr 1 462547 693821 (by norm_num) (by norm_num) (sr 3 693821 260183 (by norm_num) (by norm_num) (sr 1 260183 390275 (by norm_num) (by norm_num) (sr 1 390275 585413 (by norm_num) (by norm_num) (sr 4 585413 109765 (by norm_num) (by norm_num) (sr 4 109765 20581 (by norm_num) (by norm_num) (B 20581 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))
theorem R101407 : Reach 101407 := (sr 1 101407 152111 (by norm_num) (by norm_num) (sr 1 152111 228167 (by norm_num) (by norm_num) (sr 1 228167 342251 (by norm_num) (by norm_num) (sr 1 342251 513377 (by norm_num) (by norm_num) (sr 2 513377 385033 (by norm_num) (by norm_num) (sr 2 385033 288775 (by norm_num) (by norm_num) (sr 1 288775 433163 (by norm_num) (by norm_num) (sr 1 433163 649745 (by norm_num) (by norm_num) (sr 2 649745 487309 (by norm_num) (by norm_num) (sr 3 487309 182741 (by norm_num) (by norm_num) (sr 7 182741 4283 (by norm_num) (by norm_num) (B 4283 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R101411 : Reach 101411 := (sr 1 101411 152117 (by norm_num) (by norm_num) (sr 5 152117 14261 (by norm_num) (by norm_num) (B 14261 (by norm_num) (by norm_num) (by norm_num))))
theorem R101415 : Reach 101415 := (sr 1 101415 152123 (by norm_num) (by norm_num) (sr 1 152123 228185 (by norm_num) (by norm_num) (sr 2 228185 171139 (by norm_num) (by norm_num) (sr 1 171139 256709 (by norm_num) (by norm_num) (sr 4 256709 48133 (by norm_num) (by norm_num) (B 48133 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101419 : Reach 101419 := (sr 1 101419 152129 (by norm_num) (by norm_num) (sr 2 152129 114097 (by norm_num) (by norm_num) (sr 2 114097 85573 (by norm_num) (by norm_num) (B 85573 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101423 : Reach 101423 := (sr 1 101423 152135 (by norm_num) (by norm_num) (sr 1 152135 228203 (by norm_num) (by norm_num) (sr 1 228203 342305 (by norm_num) (by norm_num) (sr 2 342305 256729 (by norm_num) (by norm_num) (sr 2 256729 192547 (by norm_num) (by norm_num) (sr 1 192547 288821 (by norm_num) (by norm_num) (sr 5 288821 27077 (by norm_num) (by norm_num) (B 27077 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R101427 : Reach 101427 := (sr 1 101427 152141 (by norm_num) (by norm_num) (sr 3 152141 57053 (by norm_num) (by norm_num) (B 57053 (by norm_num) (by norm_num) (by norm_num))))
theorem R101431 : Reach 101431 := (sr 1 101431 152147 (by norm_num) (by norm_num) (sr 1 152147 228221 (by norm_num) (by norm_num) (sr 3 228221 85583 (by norm_num) (by norm_num) (B 85583 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101435 : Reach 101435 := (sr 1 101435 152153 (by norm_num) (by norm_num) (sr 2 152153 114115 (by norm_num) (by norm_num) (sr 1 114115 171173 (by norm_num) (by norm_num) (sr 4 171173 32095 (by norm_num) (by norm_num) (B 32095 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101439 : Reach 101439 := (sr 1 101439 152159 (by norm_num) (by norm_num) (sr 1 152159 228239 (by norm_num) (by norm_num) (sr 1 228239 342359 (by norm_num) (by norm_num) (sr 1 342359 513539 (by norm_num) (by norm_num) (sr 1 513539 770309 (by norm_num) (by norm_num) (sr 4 770309 144433 (by norm_num) (by norm_num) (sr 2 144433 108325 (by norm_num) (by norm_num) (sr 4 108325 20311 (by norm_num) (by norm_num) (B 20311 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R101443 : Reach 101443 := (sr 1 101443 152165 (by norm_num) (by norm_num) (sr 4 152165 28531 (by norm_num) (by norm_num) (B 28531 (by norm_num) (by norm_num) (by norm_num))))
theorem R101447 : Reach 101447 := (sr 1 101447 152171 (by norm_num) (by norm_num) (sr 1 152171 228257 (by norm_num) (by norm_num) (sr 2 228257 171193 (by norm_num) (by norm_num) (sr 2 171193 128395 (by norm_num) (by norm_num) (sr 1 128395 192593 (by norm_num) (by norm_num) (sr 2 192593 144445 (by norm_num) (by norm_num) (sr 3 144445 54167 (by norm_num) (by norm_num) (B 54167 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R101451 : Reach 101451 := (sr 1 101451 152177 (by norm_num) (by norm_num) (sr 2 152177 114133 (by norm_num) (by norm_num) (sr 7 114133 2675 (by norm_num) (by norm_num) (B 2675 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101455 : Reach 101455 := (sr 1 101455 152183 (by norm_num) (by norm_num) (sr 1 152183 228275 (by norm_num) (by norm_num) (sr 1 228275 342413 (by norm_num) (by norm_num) (sr 3 342413 128405 (by norm_num) (by norm_num) (sr 6 128405 6019 (by norm_num) (by norm_num) (B 6019 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101459 : Reach 101459 := (sr 1 101459 152189 (by norm_num) (by norm_num) (sr 3 152189 57071 (by norm_num) (by norm_num) (B 57071 (by norm_num) (by norm_num) (by norm_num))))
theorem R101463 : Reach 101463 := (sr 1 101463 152195 (by norm_num) (by norm_num) (sr 1 152195 228293 (by norm_num) (by norm_num) (sr 4 228293 42805 (by norm_num) (by norm_num) (B 42805 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101467 : Reach 101467 := (sr 1 101467 152201 (by norm_num) (by norm_num) (sr 2 152201 114151 (by norm_num) (by norm_num) (sr 1 114151 171227 (by norm_num) (by norm_num) (sr 1 171227 256841 (by norm_num) (by norm_num) (sr 2 256841 192631 (by norm_num) (by norm_num) (sr 1 192631 288947 (by norm_num) (by norm_num) (sr 1 288947 433421 (by norm_num) (by norm_num) (sr 3 433421 162533 (by norm_num) (by norm_num) (sr 4 162533 30475 (by norm_num) (by norm_num) (B 30475 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R101471 : Reach 101471 := (sr 1 101471 152207 (by norm_num) (by norm_num) (sr 1 152207 228311 (by norm_num) (by norm_num) (sr 1 228311 342467 (by norm_num) (by norm_num) (sr 1 342467 513701 (by norm_num) (by norm_num) (sr 4 513701 96319 (by norm_num) (by norm_num) (B 96319 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101475 : Reach 101475 := (sr 1 101475 152213 (by norm_num) (by norm_num) (sr 6 152213 7135 (by norm_num) (by norm_num) (B 7135 (by norm_num) (by norm_num) (by norm_num))))
theorem R101479 : Reach 101479 := (sr 1 101479 152219 (by norm_num) (by norm_num) (sr 1 152219 228329 (by norm_num) (by norm_num) (sr 2 228329 171247 (by norm_num) (by norm_num) (sr 1 171247 256871 (by norm_num) (by norm_num) (sr 1 256871 385307 (by norm_num) (by norm_num) (sr 1 385307 577961 (by norm_num) (by norm_num) (sr 2 577961 433471 (by norm_num) (by norm_num) (sr 1 433471 650207 (by norm_num) (by norm_num) (sr 1 650207 975311 (by norm_num) (by norm_num) (sr 1 975311 1462967 (by norm_num) (by norm_num) (sr 1 1462967 2194451 (by norm_num) (by norm_num) (sr 1 2194451 3291677 (by norm_num) (by norm_num) (sr 3 3291677 1234379 (by norm_num) (by norm_num) (sr 1 1234379 1851569 (by norm_num) (by norm_num) (sr 2 1851569 1388677 (by norm_num) (by norm_num) (sr 4 1388677 260377 (by norm_num) (by norm_num) (sr 2 260377 195283 (by norm_num) (by norm_num) (sr 1 195283 292925 (by norm_num) (by norm_num) (sr 3 292925 109847 (by norm_num) (by norm_num) (sr 1 109847 164771 (by norm_num) (by norm_num) (sr 1 164771 247157 (by norm_num) (by norm_num) (sr 5 247157 23171 (by norm_num) (by norm_num) (B 23171 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R101483 : Reach 101483 := (sr 1 101483 152225 (by norm_num) (by norm_num) (sr 2 152225 114169 (by norm_num) (by norm_num) (sr 2 114169 85627 (by norm_num) (by norm_num) (B 85627 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101487 : Reach 101487 := (sr 1 101487 152231 (by norm_num) (by norm_num) (sr 1 152231 228347 (by norm_num) (by norm_num) (sr 1 228347 342521 (by norm_num) (by norm_num) (sr 2 342521 256891 (by norm_num) (by norm_num) (sr 1 256891 385337 (by norm_num) (by norm_num) (sr 2 385337 289003 (by norm_num) (by norm_num) (sr 1 289003 433505 (by norm_num) (by norm_num) (sr 2 433505 325129 (by norm_num) (by norm_num) (sr 2 325129 243847 (by norm_num) (by norm_num) (sr 1 243847 365771 (by norm_num) (by norm_num) (sr 1 365771 548657 (by norm_num) (by norm_num) (sr 2 548657 411493 (by norm_num) (by norm_num) (sr 4 411493 77155 (by norm_num) (by norm_num) (B 77155 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R101491 : Reach 101491 := (sr 1 101491 152237 (by norm_num) (by norm_num) (sr 3 152237 57089 (by norm_num) (by norm_num) (B 57089 (by norm_num) (by norm_num) (by norm_num))))
theorem R101495 : Reach 101495 := (sr 1 101495 152243 (by norm_num) (by norm_num) (sr 1 152243 228365 (by norm_num) (by norm_num) (sr 3 228365 85637 (by norm_num) (by norm_num) (B 85637 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101499 : Reach 101499 := (sr 1 101499 152249 (by norm_num) (by norm_num) (sr 2 152249 114187 (by norm_num) (by norm_num) (sr 1 114187 171281 (by norm_num) (by norm_num) (sr 2 171281 128461 (by norm_num) (by norm_num) (sr 3 128461 48173 (by norm_num) (by norm_num) (B 48173 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101503 : Reach 101503 := (sr 1 101503 152255 (by norm_num) (by norm_num) (sr 1 152255 228383 (by norm_num) (by norm_num) (sr 1 228383 342575 (by norm_num) (by norm_num) (sr 1 342575 513863 (by norm_num) (by norm_num) (sr 1 513863 770795 (by norm_num) (by norm_num) (sr 1 770795 1156193 (by norm_num) (by norm_num) (sr 2 1156193 867145 (by norm_num) (by norm_num) (sr 2 867145 650359 (by norm_num) (by norm_num) (sr 1 650359 975539 (by norm_num) (by norm_num) (sr 1 975539 1463309 (by norm_num) (by norm_num) (sr 3 1463309 548741 (by norm_num) (by norm_num) (sr 4 548741 102889 (by norm_num) (by norm_num) (sr 2 102889 77167 (by norm_num) (by norm_num) (B 77167 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R101507 : Reach 101507 := (sr 1 101507 152261 (by norm_num) (by norm_num) (sr 4 152261 28549 (by norm_num) (by norm_num) (B 28549 (by norm_num) (by norm_num) (by norm_num))))
theorem R101511 : Reach 101511 := (sr 1 101511 152267 (by norm_num) (by norm_num) (sr 1 152267 228401 (by norm_num) (by norm_num) (sr 2 228401 171301 (by norm_num) (by norm_num) (sr 4 171301 32119 (by norm_num) (by norm_num) (B 32119 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101515 : Reach 101515 := (sr 1 101515 152273 (by norm_num) (by norm_num) (sr 2 152273 114205 (by norm_num) (by norm_num) (sr 3 114205 42827 (by norm_num) (by norm_num) (B 42827 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101519 : Reach 101519 := (sr 1 101519 152279 (by norm_num) (by norm_num) (sr 1 152279 228419 (by norm_num) (by norm_num) (sr 1 228419 342629 (by norm_num) (by norm_num) (sr 4 342629 64243 (by norm_num) (by norm_num) (B 64243 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101523 : Reach 101523 := (sr 1 101523 152285 (by norm_num) (by norm_num) (sr 3 152285 57107 (by norm_num) (by norm_num) (B 57107 (by norm_num) (by norm_num) (by norm_num))))
theorem R101527 : Reach 101527 := (sr 1 101527 152291 (by norm_num) (by norm_num) (sr 1 152291 228437 (by norm_num) (by norm_num) (sr 8 228437 2677 (by norm_num) (by norm_num) (B 2677 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101531 : Reach 101531 := (sr 1 101531 152297 (by norm_num) (by norm_num) (sr 2 152297 114223 (by norm_num) (by norm_num) (sr 1 114223 171335 (by norm_num) (by norm_num) (sr 1 171335 257003 (by norm_num) (by norm_num) (sr 1 257003 385505 (by norm_num) (by norm_num) (sr 2 385505 289129 (by norm_num) (by norm_num) (sr 2 289129 216847 (by norm_num) (by norm_num) (sr 1 216847 325271 (by norm_num) (by norm_num) (sr 1 325271 487907 (by norm_num) (by norm_num) (sr 1 487907 731861 (by norm_num) (by norm_num) (sr 7 731861 17153 (by norm_num) (by norm_num) (B 17153 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R101535 : Reach 101535 := (sr 1 101535 152303 (by norm_num) (by norm_num) (sr 1 152303 228455 (by norm_num) (by norm_num) (sr 1 228455 342683 (by norm_num) (by norm_num) (sr 1 342683 514025 (by norm_num) (by norm_num) (sr 2 514025 385519 (by norm_num) (by norm_num) (sr 1 385519 578279 (by norm_num) (by norm_num) (sr 1 578279 867419 (by norm_num) (by norm_num) (sr 1 867419 1301129 (by norm_num) (by norm_num) (sr 2 1301129 975847 (by norm_num) (by norm_num) (sr 1 975847 1463771 (by norm_num) (by norm_num) (sr 1 1463771 2195657 (by norm_num) (by norm_num) (sr 2 2195657 1646743 (by norm_num) (by norm_num) (sr 1 1646743 2470115 (by norm_num) (by norm_num) (sr 1 2470115 3705173 (by norm_num) (by norm_num) (sr 10 3705173 10855 (by norm_num) (by norm_num) (B 10855 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R101539 : Reach 101539 := (sr 1 101539 152309 (by norm_num) (by norm_num) (sr 5 152309 14279 (by norm_num) (by norm_num) (B 14279 (by norm_num) (by norm_num) (by norm_num))))
theorem R101543 : Reach 101543 := (sr 1 101543 152315 (by norm_num) (by norm_num) (sr 1 152315 228473 (by norm_num) (by norm_num) (sr 2 228473 171355 (by norm_num) (by norm_num) (sr 1 171355 257033 (by norm_num) (by norm_num) (sr 2 257033 192775 (by norm_num) (by norm_num) (sr 1 192775 289163 (by norm_num) (by norm_num) (sr 1 289163 433745 (by norm_num) (by norm_num) (sr 2 433745 325309 (by norm_num) (by norm_num) (sr 3 325309 121991 (by norm_num) (by norm_num) (sr 1 121991 182987 (by norm_num) (by norm_num) (sr 1 182987 274481 (by norm_num) (by norm_num) (sr 2 274481 205861 (by norm_num) (by norm_num) (sr 4 205861 38599 (by norm_num) (by norm_num) (B 38599 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R101547 : Reach 101547 := (sr 1 101547 152321 (by norm_num) (by norm_num) (sr 2 152321 114241 (by norm_num) (by norm_num) (sr 2 114241 85681 (by norm_num) (by norm_num) (B 85681 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101551 : Reach 101551 := (sr 1 101551 152327 (by norm_num) (by norm_num) (sr 1 152327 228491 (by norm_num) (by norm_num) (sr 1 228491 342737 (by norm_num) (by norm_num) (sr 2 342737 257053 (by norm_num) (by norm_num) (sr 3 257053 96395 (by norm_num) (by norm_num) (B 96395 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101555 : Reach 101555 := (sr 1 101555 152333 (by norm_num) (by norm_num) (sr 3 152333 57125 (by norm_num) (by norm_num) (B 57125 (by norm_num) (by norm_num) (by norm_num))))
theorem R101559 : Reach 101559 := (sr 1 101559 152339 (by norm_num) (by norm_num) (sr 1 152339 228509 (by norm_num) (by norm_num) (sr 3 228509 85691 (by norm_num) (by norm_num) (B 85691 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101563 : Reach 101563 := (sr 1 101563 152345 (by norm_num) (by norm_num) (sr 2 152345 114259 (by norm_num) (by norm_num) (sr 1 114259 171389 (by norm_num) (by norm_num) (sr 3 171389 64271 (by norm_num) (by norm_num) (B 64271 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101567 : Reach 101567 := (sr 1 101567 152351 (by norm_num) (by norm_num) (sr 1 152351 228527 (by norm_num) (by norm_num) (sr 1 228527 342791 (by norm_num) (by norm_num) (sr 1 342791 514187 (by norm_num) (by norm_num) (sr 1 514187 771281 (by norm_num) (by norm_num) (sr 2 771281 578461 (by norm_num) (by norm_num) (sr 3 578461 216923 (by norm_num) (by norm_num) (sr 1 216923 325385 (by norm_num) (by norm_num) (sr 2 325385 244039 (by norm_num) (by norm_num) (sr 1 244039 366059 (by norm_num) (by norm_num) (sr 1 366059 549089 (by norm_num) (by norm_num) (sr 2 549089 411817 (by norm_num) (by norm_num) (sr 2 411817 308863 (by norm_num) (by norm_num) (sr 1 308863 463295 (by norm_num) (by norm_num) (sr 1 463295 694943 (by norm_num) (by norm_num) (sr 1 694943 1042415 (by norm_num) (by norm_num) (sr 1 1042415 1563623 (by norm_num) (by norm_num) (sr 1 1563623 2345435 (by norm_num) (by norm_num) (sr 1 2345435 3518153 (by norm_num) (by norm_num) (sr 2 3518153 2638615 (by norm_num) (by norm_num) (sr 1 2638615 3957923 (by norm_num) (by norm_num) (sr 1 3957923 5936885 (by norm_num) (by norm_num) (sr 5 5936885 556583 (by norm_num) (by norm_num) (sr 1 556583 834875 (by norm_num) (by norm_num) (sr 1 834875 1252313 (by norm_num) (by norm_num) (sr 2 1252313 939235 (by norm_num) (by norm_num) (sr 1 939235 1408853 (by norm_num) (by norm_num) (sr 9 1408853 8255 (by norm_num) (by norm_num) (B 8255 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))
theorem R101571 : Reach 101571 := (sr 1 101571 152357 (by norm_num) (by norm_num) (sr 4 152357 28567 (by norm_num) (by norm_num) (B 28567 (by norm_num) (by norm_num) (by norm_num))))
theorem R101575 : Reach 101575 := (sr 1 101575 152363 (by norm_num) (by norm_num) (sr 1 152363 228545 (by norm_num) (by norm_num) (sr 2 228545 171409 (by norm_num) (by norm_num) (sr 2 171409 128557 (by norm_num) (by norm_num) (sr 3 128557 48209 (by norm_num) (by norm_num) (B 48209 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101579 : Reach 101579 := (sr 1 101579 152369 (by norm_num) (by norm_num) (sr 2 152369 114277 (by norm_num) (by norm_num) (sr 4 114277 21427 (by norm_num) (by norm_num) (B 21427 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101583 : Reach 101583 := (sr 1 101583 152375 (by norm_num) (by norm_num) (sr 1 152375 228563 (by norm_num) (by norm_num) (sr 1 228563 342845 (by norm_num) (by norm_num) (sr 3 342845 128567 (by norm_num) (by norm_num) (sr 1 128567 192851 (by norm_num) (by norm_num) (sr 1 192851 289277 (by norm_num) (by norm_num) (sr 3 289277 108479 (by norm_num) (by norm_num) (sr 1 108479 162719 (by norm_num) (by norm_num) (sr 1 162719 244079 (by norm_num) (by norm_num) (sr 1 244079 366119 (by norm_num) (by norm_num) (sr 1 366119 549179 (by norm_num) (by norm_num) (sr 1 549179 823769 (by norm_num) (by norm_num) (sr 2 823769 617827 (by norm_num) (by norm_num) (sr 1 617827 926741 (by norm_num) (by norm_num) (sr 6 926741 43441 (by norm_num) (by norm_num) (B 43441 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R101587 : Reach 101587 := (sr 1 101587 152381 (by norm_num) (by norm_num) (sr 3 152381 57143 (by norm_num) (by norm_num) (B 57143 (by norm_num) (by norm_num) (by norm_num))))
theorem R101591 : Reach 101591 := (sr 1 101591 152387 (by norm_num) (by norm_num) (sr 1 152387 228581 (by norm_num) (by norm_num) (sr 4 228581 42859 (by norm_num) (by norm_num) (B 42859 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101595 : Reach 101595 := (sr 1 101595 152393 (by norm_num) (by norm_num) (sr 2 152393 114295 (by norm_num) (by norm_num) (sr 1 114295 171443 (by norm_num) (by norm_num) (sr 1 171443 257165 (by norm_num) (by norm_num) (sr 3 257165 96437 (by norm_num) (by norm_num) (B 96437 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101599 : Reach 101599 := (sr 1 101599 152399 (by norm_num) (by norm_num) (sr 1 152399 228599 (by norm_num) (by norm_num) (sr 1 228599 342899 (by norm_num) (by norm_num) (sr 1 342899 514349 (by norm_num) (by norm_num) (sr 3 514349 192881 (by norm_num) (by norm_num) (sr 2 192881 144661 (by norm_num) (by norm_num) (sr 6 144661 6781 (by norm_num) (by norm_num) (B 6781 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R101603 : Reach 101603 := (sr 1 101603 152405 (by norm_num) (by norm_num) (sr 9 152405 893 (by norm_num) (by norm_num) (B 893 (by norm_num) (by norm_num) (by norm_num))))
theorem R101607 : Reach 101607 := (sr 1 101607 152411 (by norm_num) (by norm_num) (sr 1 152411 228617 (by norm_num) (by norm_num) (sr 2 228617 171463 (by norm_num) (by norm_num) (sr 1 171463 257195 (by norm_num) (by norm_num) (sr 1 257195 385793 (by norm_num) (by norm_num) (sr 2 385793 289345 (by norm_num) (by norm_num) (sr 2 289345 217009 (by norm_num) (by norm_num) (sr 2 217009 162757 (by norm_num) (by norm_num) (sr 4 162757 30517 (by norm_num) (by norm_num) (B 30517 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R101611 : Reach 101611 := (sr 1 101611 152417 (by norm_num) (by norm_num) (sr 2 152417 114313 (by norm_num) (by norm_num) (sr 2 114313 85735 (by norm_num) (by norm_num) (B 85735 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101615 : Reach 101615 := (sr 1 101615 152423 (by norm_num) (by norm_num) (sr 1 152423 228635 (by norm_num) (by norm_num) (sr 1 228635 342953 (by norm_num) (by norm_num) (sr 2 342953 257215 (by norm_num) (by norm_num) (sr 1 257215 385823 (by norm_num) (by norm_num) (sr 1 385823 578735 (by norm_num) (by norm_num) (sr 1 578735 868103 (by norm_num) (by norm_num) (sr 1 868103 1302155 (by norm_num) (by norm_num) (sr 1 1302155 1953233 (by norm_num) (by norm_num) (sr 2 1953233 1464925 (by norm_num) (by norm_num) (sr 3 1464925 549347 (by norm_num) (by norm_num) (sr 1 549347 824021 (by norm_num) (by norm_num) (sr 7 824021 19313 (by norm_num) (by norm_num) (B 19313 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R101619 : Reach 101619 := (sr 1 101619 152429 (by norm_num) (by norm_num) (sr 3 152429 57161 (by norm_num) (by norm_num) (B 57161 (by norm_num) (by norm_num) (by norm_num))))
theorem R101623 : Reach 101623 := (sr 1 101623 152435 (by norm_num) (by norm_num) (sr 1 152435 228653 (by norm_num) (by norm_num) (sr 3 228653 85745 (by norm_num) (by norm_num) (B 85745 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101627 : Reach 101627 := (sr 1 101627 152441 (by norm_num) (by norm_num) (sr 2 152441 114331 (by norm_num) (by norm_num) (sr 1 114331 171497 (by norm_num) (by norm_num) (sr 2 171497 128623 (by norm_num) (by norm_num) (sr 1 128623 192935 (by norm_num) (by norm_num) (sr 1 192935 289403 (by norm_num) (by norm_num) (sr 1 289403 434105 (by norm_num) (by norm_num) (sr 2 434105 325579 (by norm_num) (by norm_num) (sr 1 325579 488369 (by norm_num) (by norm_num) (sr 2 488369 366277 (by norm_num) (by norm_num) (sr 4 366277 68677 (by norm_num) (by norm_num) (B 68677 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R101631 : Reach 101631 := (sr 1 101631 152447 (by norm_num) (by norm_num) (sr 1 152447 228671 (by norm_num) (by norm_num) (sr 1 228671 343007 (by norm_num) (by norm_num) (sr 1 343007 514511 (by norm_num) (by norm_num) (sr 1 514511 771767 (by norm_num) (by norm_num) (sr 1 771767 1157651 (by norm_num) (by norm_num) (sr 1 1157651 1736477 (by norm_num) (by norm_num) (sr 3 1736477 651179 (by norm_num) (by norm_num) (sr 1 651179 976769 (by norm_num) (by norm_num) (sr 2 976769 732577 (by norm_num) (by norm_num) (sr 2 732577 549433 (by norm_num) (by norm_num) (sr 2 549433 412075 (by norm_num) (by norm_num) (sr 1 412075 618113 (by norm_num) (by norm_num) (sr 2 618113 463585 (by norm_num) (by norm_num) (sr 2 463585 347689 (by norm_num) (by norm_num) (sr 2 347689 260767 (by norm_num) (by norm_num) (sr 1 260767 391151 (by norm_num) (by norm_num) (sr 1 391151 586727 (by norm_num) (by norm_num) (sr 1 586727 880091 (by norm_num) (by norm_num) (sr 1 880091 1320137 (by norm_num) (by norm_num) (sr 2 1320137 990103 (by norm_num) (by norm_num) (sr 1 990103 1485155 (by norm_num) (by norm_num) (sr 1 1485155 2227733 (by norm_num) (by norm_num) (sr 6 2227733 104425 (by norm_num) (by norm_num) (sr 2 104425 78319 (by norm_num) (by norm_num) (B 78319 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))
theorem R101635 : Reach 101635 := (sr 1 101635 152453 (by norm_num) (by norm_num) (sr 4 152453 28585 (by norm_num) (by norm_num) (B 28585 (by norm_num) (by norm_num) (by norm_num))))
theorem R101639 : Reach 101639 := (sr 1 101639 152459 (by norm_num) (by norm_num) (sr 1 152459 228689 (by norm_num) (by norm_num) (sr 2 228689 171517 (by norm_num) (by norm_num) (sr 3 171517 64319 (by norm_num) (by norm_num) (B 64319 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101643 : Reach 101643 := (sr 1 101643 152465 (by norm_num) (by norm_num) (sr 2 152465 114349 (by norm_num) (by norm_num) (sr 3 114349 42881 (by norm_num) (by norm_num) (B 42881 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101647 : Reach 101647 := (sr 1 101647 152471 (by norm_num) (by norm_num) (sr 1 152471 228707 (by norm_num) (by norm_num) (sr 1 228707 343061 (by norm_num) (by norm_num) (sr 6 343061 16081 (by norm_num) (by norm_num) (B 16081 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101651 : Reach 101651 := (sr 1 101651 152477 (by norm_num) (by norm_num) (sr 3 152477 57179 (by norm_num) (by norm_num) (B 57179 (by norm_num) (by norm_num) (by norm_num))))
theorem R101655 : Reach 101655 := (sr 1 101655 152483 (by norm_num) (by norm_num) (sr 1 152483 228725 (by norm_num) (by norm_num) (sr 5 228725 21443 (by norm_num) (by norm_num) (B 21443 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101659 : Reach 101659 := (sr 1 101659 152489 (by norm_num) (by norm_num) (sr 2 152489 114367 (by norm_num) (by norm_num) (sr 1 114367 171551 (by norm_num) (by norm_num) (sr 1 171551 257327 (by norm_num) (by norm_num) (sr 1 257327 385991 (by norm_num) (by norm_num) (sr 1 385991 578987 (by norm_num) (by norm_num) (sr 1 578987 868481 (by norm_num) (by norm_num) (sr 2 868481 651361 (by norm_num) (by norm_num) (sr 2 651361 488521 (by norm_num) (by norm_num) (sr 2 488521 366391 (by norm_num) (by norm_num) (sr 1 366391 549587 (by norm_num) (by norm_num) (sr 1 549587 824381 (by norm_num) (by norm_num) (sr 3 824381 309143 (by norm_num) (by norm_num) (sr 1 309143 463715 (by norm_num) (by norm_num) (sr 1 463715 695573 (by norm_num) (by norm_num) (sr 6 695573 32605 (by norm_num) (by norm_num) (B 32605 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))
theorem R101663 : Reach 101663 := (sr 1 101663 152495 (by norm_num) (by norm_num) (sr 1 152495 228743 (by norm_num) (by norm_num) (sr 1 228743 343115 (by norm_num) (by norm_num) (sr 1 343115 514673 (by norm_num) (by norm_num) (sr 2 514673 386005 (by norm_num) (by norm_num) (sr 7 386005 9047 (by norm_num) (by norm_num) (B 9047 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R101667 : Reach 101667 := (sr 1 101667 152501 (by norm_num) (by norm_num) (sr 5 152501 14297 (by norm_num) (by norm_num) (B 14297 (by norm_num) (by norm_num) (by norm_num))))
theorem R101671 : Reach 101671 := (sr 1 101671 152507 (by norm_num) (by norm_num) (sr 1 152507 228761 (by norm_num) (by norm_num) (sr 2 228761 171571 (by norm_num) (by norm_num) (sr 1 171571 257357 (by norm_num) (by norm_num) (sr 3 257357 96509 (by norm_num) (by norm_num) (B 96509 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101675 : Reach 101675 := (sr 1 101675 152513 (by norm_num) (by norm_num) (sr 2 152513 114385 (by norm_num) (by norm_num) (sr 2 114385 85789 (by norm_num) (by norm_num) (B 85789 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101679 : Reach 101679 := (sr 1 101679 152519 (by norm_num) (by norm_num) (sr 1 152519 228779 (by norm_num) (by norm_num) (sr 1 228779 343169 (by norm_num) (by norm_num) (sr 2 343169 257377 (by norm_num) (by norm_num) (sr 2 257377 193033 (by norm_num) (by norm_num) (sr 2 193033 144775 (by norm_num) (by norm_num) (sr 1 144775 217163 (by norm_num) (by norm_num) (sr 1 217163 325745 (by norm_num) (by norm_num) (sr 2 325745 244309 (by norm_num) (by norm_num) (sr 8 244309 2863 (by norm_num) (by norm_num) (B 2863 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R101683 : Reach 101683 := (sr 1 101683 152525 (by norm_num) (by norm_num) (sr 3 152525 57197 (by norm_num) (by norm_num) (B 57197 (by norm_num) (by norm_num) (by norm_num))))
theorem R101687 : Reach 101687 := (sr 1 101687 152531 (by norm_num) (by norm_num) (sr 1 152531 228797 (by norm_num) (by norm_num) (sr 3 228797 85799 (by norm_num) (by norm_num) (B 85799 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101691 : Reach 101691 := (sr 1 101691 152537 (by norm_num) (by norm_num) (sr 2 152537 114403 (by norm_num) (by norm_num) (sr 1 114403 171605 (by norm_num) (by norm_num) (sr 8 171605 2011 (by norm_num) (by norm_num) (B 2011 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101695 : Reach 101695 := (sr 1 101695 152543 (by norm_num) (by norm_num) (sr 1 152543 228815 (by norm_num) (by norm_num) (sr 1 228815 343223 (by norm_num) (by norm_num) (sr 1 343223 514835 (by norm_num) (by norm_num) (sr 1 514835 772253 (by norm_num) (by norm_num) (sr 3 772253 289595 (by norm_num) (by norm_num) (sr 1 289595 434393 (by norm_num) (by norm_num) (sr 2 434393 325795 (by norm_num) (by norm_num) (sr 1 325795 488693 (by norm_num) (by norm_num) (sr 5 488693 45815 (by norm_num) (by norm_num) (B 45815 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R101699 : Reach 101699 := (sr 1 101699 152549 (by norm_num) (by norm_num) (sr 4 152549 28603 (by norm_num) (by norm_num) (B 28603 (by norm_num) (by norm_num) (by norm_num))))
theorem R101703 : Reach 101703 := (sr 1 101703 152555 (by norm_num) (by norm_num) (sr 1 152555 228833 (by norm_num) (by norm_num) (sr 2 228833 171625 (by norm_num) (by norm_num) (sr 2 171625 128719 (by norm_num) (by norm_num) (sr 1 128719 193079 (by norm_num) (by norm_num) (sr 1 193079 289619 (by norm_num) (by norm_num) (sr 1 289619 434429 (by norm_num) (by norm_num) (sr 3 434429 162911 (by norm_num) (by norm_num) (sr 1 162911 244367 (by norm_num) (by norm_num) (sr 1 244367 366551 (by norm_num) (by norm_num) (sr 1 366551 549827 (by norm_num) (by norm_num) (sr 1 549827 824741 (by norm_num) (by norm_num) (sr 4 824741 154639 (by norm_num) (by norm_num) (sr 1 154639 231959 (by norm_num) (by norm_num) (sr 1 231959 347939 (by norm_num) (by norm_num) (sr 1 347939 521909 (by norm_num) (by norm_num) (sr 5 521909 48929 (by norm_num) (by norm_num) (B 48929 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))
theorem R101707 : Reach 101707 := (sr 1 101707 152561 (by norm_num) (by norm_num) (sr 2 152561 114421 (by norm_num) (by norm_num) (sr 5 114421 10727 (by norm_num) (by norm_num) (B 10727 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101711 : Reach 101711 := (sr 1 101711 152567 (by norm_num) (by norm_num) (sr 1 152567 228851 (by norm_num) (by norm_num) (sr 1 228851 343277 (by norm_num) (by norm_num) (sr 3 343277 128729 (by norm_num) (by norm_num) (sr 2 128729 96547 (by norm_num) (by norm_num) (B 96547 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101715 : Reach 101715 := (sr 1 101715 152573 (by norm_num) (by norm_num) (sr 3 152573 57215 (by norm_num) (by norm_num) (B 57215 (by norm_num) (by norm_num) (by norm_num))))
theorem R101719 : Reach 101719 := (sr 1 101719 152579 (by norm_num) (by norm_num) (sr 1 152579 228869 (by norm_num) (by norm_num) (sr 4 228869 42913 (by norm_num) (by norm_num) (B 42913 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101723 : Reach 101723 := (sr 1 101723 152585 (by norm_num) (by norm_num) (sr 2 152585 114439 (by norm_num) (by norm_num) (sr 1 114439 171659 (by norm_num) (by norm_num) (sr 1 171659 257489 (by norm_num) (by norm_num) (sr 2 257489 193117 (by norm_num) (by norm_num) (sr 3 193117 72419 (by norm_num) (by norm_num) (B 72419 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R101727 : Reach 101727 := (sr 1 101727 152591 (by norm_num) (by norm_num) (sr 1 152591 228887 (by norm_num) (by norm_num) (sr 1 228887 343331 (by norm_num) (by norm_num) (sr 1 343331 514997 (by norm_num) (by norm_num) (sr 5 514997 48281 (by norm_num) (by norm_num) (B 48281 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101731 : Reach 101731 := (sr 1 101731 152597 (by norm_num) (by norm_num) (sr 6 152597 7153 (by norm_num) (by norm_num) (B 7153 (by norm_num) (by norm_num) (by norm_num))))
theorem R101735 : Reach 101735 := (sr 1 101735 152603 (by norm_num) (by norm_num) (sr 1 152603 228905 (by norm_num) (by norm_num) (sr 2 228905 171679 (by norm_num) (by norm_num) (sr 1 171679 257519 (by norm_num) (by norm_num) (sr 1 257519 386279 (by norm_num) (by norm_num) (sr 1 386279 579419 (by norm_num) (by norm_num) (sr 1 579419 869129 (by norm_num) (by norm_num) (sr 2 869129 651847 (by norm_num) (by norm_num) (sr 1 651847 977771 (by norm_num) (by norm_num) (sr 1 977771 1466657 (by norm_num) (by norm_num) (sr 2 1466657 1099993 (by norm_num) (by norm_num) (sr 2 1099993 824995 (by norm_num) (by norm_num) (sr 1 824995 1237493 (by norm_num) (by norm_num) (sr 5 1237493 116015 (by norm_num) (by norm_num) (sr 1 116015 174023 (by norm_num) (by norm_num) (sr 1 174023 261035 (by norm_num) (by norm_num) (sr 1 261035 391553 (by norm_num) (by norm_num) (sr 2 391553 293665 (by norm_num) (by norm_num) (sr 2 293665 220249 (by norm_num) (by norm_num) (sr 2 220249 165187 (by norm_num) (by norm_num) (sr 1 165187 247781 (by norm_num) (by norm_num) (sr 4 247781 46459 (by norm_num) (by norm_num) (B 46459 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R101739 : Reach 101739 := (sr 1 101739 152609 (by norm_num) (by norm_num) (sr 2 152609 114457 (by norm_num) (by norm_num) (sr 2 114457 85843 (by norm_num) (by norm_num) (B 85843 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101743 : Reach 101743 := (sr 1 101743 152615 (by norm_num) (by norm_num) (sr 1 152615 228923 (by norm_num) (by norm_num) (sr 1 228923 343385 (by norm_num) (by norm_num) (sr 2 343385 257539 (by norm_num) (by norm_num) (sr 1 257539 386309 (by norm_num) (by norm_num) (sr 4 386309 72433 (by norm_num) (by norm_num) (B 72433 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R101747 : Reach 101747 := (sr 1 101747 152621 (by norm_num) (by norm_num) (sr 3 152621 57233 (by norm_num) (by norm_num) (B 57233 (by norm_num) (by norm_num) (by norm_num))))
theorem R101751 : Reach 101751 := (sr 1 101751 152627 (by norm_num) (by norm_num) (sr 1 152627 228941 (by norm_num) (by norm_num) (sr 3 228941 85853 (by norm_num) (by norm_num) (B 85853 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101755 : Reach 101755 := (sr 1 101755 152633 (by norm_num) (by norm_num) (sr 2 152633 114475 (by norm_num) (by norm_num) (sr 1 114475 171713 (by norm_num) (by norm_num) (sr 2 171713 128785 (by norm_num) (by norm_num) (sr 2 128785 96589 (by norm_num) (by norm_num) (B 96589 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101759 : Reach 101759 := (sr 1 101759 152639 (by norm_num) (by norm_num) (sr 1 152639 228959 (by norm_num) (by norm_num) (sr 1 228959 343439 (by norm_num) (by norm_num) (sr 1 343439 515159 (by norm_num) (by norm_num) (sr 1 515159 772739 (by norm_num) (by norm_num) (sr 1 772739 1159109 (by norm_num) (by norm_num) (sr 4 1159109 217333 (by norm_num) (by norm_num) (sr 5 217333 20375 (by norm_num) (by norm_num) (B 20375 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R101763 : Reach 101763 := (sr 1 101763 152645 (by norm_num) (by norm_num) (sr 4 152645 28621 (by norm_num) (by norm_num) (B 28621 (by norm_num) (by norm_num) (by norm_num))))
theorem R101767 : Reach 101767 := (sr 1 101767 152651 (by norm_num) (by norm_num) (sr 1 152651 228977 (by norm_num) (by norm_num) (sr 2 228977 171733 (by norm_num) (by norm_num) (sr 7 171733 4025 (by norm_num) (by norm_num) (B 4025 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101771 : Reach 101771 := (sr 1 101771 152657 (by norm_num) (by norm_num) (sr 2 152657 114493 (by norm_num) (by norm_num) (sr 3 114493 42935 (by norm_num) (by norm_num) (B 42935 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101775 : Reach 101775 := (sr 1 101775 152663 (by norm_num) (by norm_num) (sr 1 152663 228995 (by norm_num) (by norm_num) (sr 1 228995 343493 (by norm_num) (by norm_num) (sr 4 343493 64405 (by norm_num) (by norm_num) (B 64405 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101779 : Reach 101779 := (sr 1 101779 152669 (by norm_num) (by norm_num) (sr 3 152669 57251 (by norm_num) (by norm_num) (B 57251 (by norm_num) (by norm_num) (by norm_num))))
theorem R101783 : Reach 101783 := (sr 1 101783 152675 (by norm_num) (by norm_num) (sr 1 152675 229013 (by norm_num) (by norm_num) (sr 6 229013 10735 (by norm_num) (by norm_num) (B 10735 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101787 : Reach 101787 := (sr 1 101787 152681 (by norm_num) (by norm_num) (sr 2 152681 114511 (by norm_num) (by norm_num) (sr 1 114511 171767 (by norm_num) (by norm_num) (sr 1 171767 257651 (by norm_num) (by norm_num) (sr 1 257651 386477 (by norm_num) (by norm_num) (sr 3 386477 144929 (by norm_num) (by norm_num) (sr 2 144929 108697 (by norm_num) (by norm_num) (sr 2 108697 81523 (by norm_num) (by norm_num) (B 81523 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R101791 : Reach 101791 := (sr 1 101791 152687 (by norm_num) (by norm_num) (sr 1 152687 229031 (by norm_num) (by norm_num) (sr 1 229031 343547 (by norm_num) (by norm_num) (sr 1 343547 515321 (by norm_num) (by norm_num) (sr 2 515321 386491 (by norm_num) (by norm_num) (sr 1 386491 579737 (by norm_num) (by norm_num) (sr 2 579737 434803 (by norm_num) (by norm_num) (sr 1 434803 652205 (by norm_num) (by norm_num) (sr 3 652205 244577 (by norm_num) (by norm_num) (sr 2 244577 183433 (by norm_num) (by norm_num) (sr 2 183433 137575 (by norm_num) (by norm_num) (sr 1 137575 206363 (by norm_num) (by norm_num) (sr 1 206363 309545 (by norm_num) (by norm_num) (sr 2 309545 232159 (by norm_num) (by norm_num) (sr 1 232159 348239 (by norm_num) (by norm_num) (sr 1 348239 522359 (by norm_num) (by norm_num) (sr 1 522359 783539 (by norm_num) (by norm_num) (sr 1 783539 1175309 (by norm_num) (by norm_num) (sr 3 1175309 440741 (by norm_num) (by norm_num) (sr 4 440741 82639 (by norm_num) (by norm_num) (B 82639 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))
theorem R101795 : Reach 101795 := (sr 1 101795 152693 (by norm_num) (by norm_num) (sr 5 152693 14315 (by norm_num) (by norm_num) (B 14315 (by norm_num) (by norm_num) (by norm_num))))
theorem R101799 : Reach 101799 := (sr 1 101799 152699 (by norm_num) (by norm_num) (sr 1 152699 229049 (by norm_num) (by norm_num) (sr 2 229049 171787 (by norm_num) (by norm_num) (sr 1 171787 257681 (by norm_num) (by norm_num) (sr 2 257681 193261 (by norm_num) (by norm_num) (sr 3 193261 72473 (by norm_num) (by norm_num) (B 72473 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R101803 : Reach 101803 := (sr 1 101803 152705 (by norm_num) (by norm_num) (sr 2 152705 114529 (by norm_num) (by norm_num) (sr 2 114529 85897 (by norm_num) (by norm_num) (B 85897 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101807 : Reach 101807 := (sr 1 101807 152711 (by norm_num) (by norm_num) (sr 1 152711 229067 (by norm_num) (by norm_num) (sr 1 229067 343601 (by norm_num) (by norm_num) (sr 2 343601 257701 (by norm_num) (by norm_num) (sr 4 257701 48319 (by norm_num) (by norm_num) (B 48319 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101811 : Reach 101811 := (sr 1 101811 152717 (by norm_num) (by norm_num) (sr 3 152717 57269 (by norm_num) (by norm_num) (B 57269 (by norm_num) (by norm_num) (by norm_num))))
theorem R101815 : Reach 101815 := (sr 1 101815 152723 (by norm_num) (by norm_num) (sr 1 152723 229085 (by norm_num) (by norm_num) (sr 3 229085 85907 (by norm_num) (by norm_num) (B 85907 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101819 : Reach 101819 := (sr 1 101819 152729 (by norm_num) (by norm_num) (sr 2 152729 114547 (by norm_num) (by norm_num) (sr 1 114547 171821 (by norm_num) (by norm_num) (sr 3 171821 64433 (by norm_num) (by norm_num) (B 64433 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101823 : Reach 101823 := (sr 1 101823 152735 (by norm_num) (by norm_num) (sr 1 152735 229103 (by norm_num) (by norm_num) (sr 1 229103 343655 (by norm_num) (by norm_num) (sr 1 343655 515483 (by norm_num) (by norm_num) (sr 1 515483 773225 (by norm_num) (by norm_num) (sr 2 773225 579919 (by norm_num) (by norm_num) (sr 1 579919 869879 (by norm_num) (by norm_num) (sr 1 869879 1304819 (by norm_num) (by norm_num) (sr 1 1304819 1957229 (by norm_num) (by norm_num) (sr 3 1957229 733961 (by norm_num) (by norm_num) (sr 2 733961 550471 (by norm_num) (by norm_num) (sr 1 550471 825707 (by norm_num) (by norm_num) (sr 1 825707 1238561 (by norm_num) (by norm_num) (sr 2 1238561 928921 (by norm_num) (by norm_num) (sr 2 928921 696691 (by norm_num) (by norm_num) (sr 1 696691 1045037 (by norm_num) (by norm_num) (sr 3 1045037 391889 (by norm_num) (by norm_num) (sr 2 391889 293917 (by norm_num) (by norm_num) (sr 3 293917 110219 (by norm_num) (by norm_num) (sr 1 110219 165329 (by norm_num) (by norm_num) (sr 2 165329 123997 (by norm_num) (by norm_num) (sr 3 123997 46499 (by norm_num) (by norm_num) (B 46499 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R101827 : Reach 101827 := (sr 1 101827 152741 (by norm_num) (by norm_num) (sr 4 152741 28639 (by norm_num) (by norm_num) (B 28639 (by norm_num) (by norm_num) (by norm_num))))
theorem R101831 : Reach 101831 := (sr 1 101831 152747 (by norm_num) (by norm_num) (sr 1 152747 229121 (by norm_num) (by norm_num) (sr 2 229121 171841 (by norm_num) (by norm_num) (sr 2 171841 128881 (by norm_num) (by norm_num) (sr 2 128881 96661 (by norm_num) (by norm_num) (B 96661 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101835 : Reach 101835 := (sr 1 101835 152753 (by norm_num) (by norm_num) (sr 2 152753 114565 (by norm_num) (by norm_num) (sr 4 114565 21481 (by norm_num) (by norm_num) (B 21481 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101839 : Reach 101839 := (sr 1 101839 152759 (by norm_num) (by norm_num) (sr 1 152759 229139 (by norm_num) (by norm_num) (sr 1 229139 343709 (by norm_num) (by norm_num) (sr 3 343709 128891 (by norm_num) (by norm_num) (sr 1 128891 193337 (by norm_num) (by norm_num) (sr 2 193337 145003 (by norm_num) (by norm_num) (sr 1 145003 217505 (by norm_num) (by norm_num) (sr 2 217505 163129 (by norm_num) (by norm_num) (sr 2 163129 122347 (by norm_num) (by norm_num) (sr 1 122347 183521 (by norm_num) (by norm_num) (sr 2 183521 137641 (by norm_num) (by norm_num) (sr 2 137641 103231 (by norm_num) (by norm_num) (sr 1 103231 154847 (by norm_num) (by norm_num) (sr 1 154847 232271 (by norm_num) (by norm_num) (sr 1 232271 348407 (by norm_num) (by norm_num) (sr 1 348407 522611 (by norm_num) (by norm_num) (sr 1 522611 783917 (by norm_num) (by norm_num) (sr 3 783917 293969 (by norm_num) (by norm_num) (sr 2 293969 220477 (by norm_num) (by norm_num) (sr 3 220477 82679 (by norm_num) (by norm_num) (B 82679 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))
theorem R101843 : Reach 101843 := (sr 1 101843 152765 (by norm_num) (by norm_num) (sr 3 152765 57287 (by norm_num) (by norm_num) (B 57287 (by norm_num) (by norm_num) (by norm_num))))
theorem R101847 : Reach 101847 := (sr 1 101847 152771 (by norm_num) (by norm_num) (sr 1 152771 229157 (by norm_num) (by norm_num) (sr 4 229157 42967 (by norm_num) (by norm_num) (B 42967 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101851 : Reach 101851 := (sr 1 101851 152777 (by norm_num) (by norm_num) (sr 2 152777 114583 (by norm_num) (by norm_num) (sr 1 114583 171875 (by norm_num) (by norm_num) (sr 1 171875 257813 (by norm_num) (by norm_num) (sr 6 257813 12085 (by norm_num) (by norm_num) (B 12085 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101855 : Reach 101855 := (sr 1 101855 152783 (by norm_num) (by norm_num) (sr 1 152783 229175 (by norm_num) (by norm_num) (sr 1 229175 343763 (by norm_num) (by norm_num) (sr 1 343763 515645 (by norm_num) (by norm_num) (sr 3 515645 193367 (by norm_num) (by norm_num) (sr 1 193367 290051 (by norm_num) (by norm_num) (sr 1 290051 435077 (by norm_num) (by norm_num) (sr 4 435077 81577 (by norm_num) (by norm_num) (B 81577 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R101859 : Reach 101859 := (sr 1 101859 152789 (by norm_num) (by norm_num) (sr 7 152789 3581 (by norm_num) (by norm_num) (B 3581 (by norm_num) (by norm_num) (by norm_num))))
theorem R101863 : Reach 101863 := (sr 1 101863 152795 (by norm_num) (by norm_num) (sr 1 152795 229193 (by norm_num) (by norm_num) (sr 2 229193 171895 (by norm_num) (by norm_num) (sr 1 171895 257843 (by norm_num) (by norm_num) (sr 1 257843 386765 (by norm_num) (by norm_num) (sr 3 386765 145037 (by norm_num) (by norm_num) (sr 3 145037 54389 (by norm_num) (by norm_num) (B 54389 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R101867 : Reach 101867 := (sr 1 101867 152801 (by norm_num) (by norm_num) (sr 2 152801 114601 (by norm_num) (by norm_num) (sr 2 114601 85951 (by norm_num) (by norm_num) (B 85951 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101871 : Reach 101871 := (sr 1 101871 152807 (by norm_num) (by norm_num) (sr 1 152807 229211 (by norm_num) (by norm_num) (sr 1 229211 343817 (by norm_num) (by norm_num) (sr 2 343817 257863 (by norm_num) (by norm_num) (sr 1 257863 386795 (by norm_num) (by norm_num) (sr 1 386795 580193 (by norm_num) (by norm_num) (sr 2 580193 435145 (by norm_num) (by norm_num) (sr 2 435145 326359 (by norm_num) (by norm_num) (sr 1 326359 489539 (by norm_num) (by norm_num) (sr 1 489539 734309 (by norm_num) (by norm_num) (sr 4 734309 137683 (by norm_num) (by norm_num) (sr 1 137683 206525 (by norm_num) (by norm_num) (sr 3 206525 77447 (by norm_num) (by norm_num) (B 77447 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R101875 : Reach 101875 := (sr 1 101875 152813 (by norm_num) (by norm_num) (sr 3 152813 57305 (by norm_num) (by norm_num) (B 57305 (by norm_num) (by norm_num) (by norm_num))))
theorem R101879 : Reach 101879 := (sr 1 101879 152819 (by norm_num) (by norm_num) (sr 1 152819 229229 (by norm_num) (by norm_num) (sr 3 229229 85961 (by norm_num) (by norm_num) (B 85961 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101883 : Reach 101883 := (sr 1 101883 152825 (by norm_num) (by norm_num) (sr 2 152825 114619 (by norm_num) (by norm_num) (sr 1 114619 171929 (by norm_num) (by norm_num) (sr 2 171929 128947 (by norm_num) (by norm_num) (sr 1 128947 193421 (by norm_num) (by norm_num) (sr 3 193421 72533 (by norm_num) (by norm_num) (B 72533 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R101887 : Reach 101887 := (sr 1 101887 152831 (by norm_num) (by norm_num) (sr 1 152831 229247 (by norm_num) (by norm_num) (sr 1 229247 343871 (by norm_num) (by norm_num) (sr 1 343871 515807 (by norm_num) (by norm_num) (sr 1 515807 773711 (by norm_num) (by norm_num) (sr 1 773711 1160567 (by norm_num) (by norm_num) (sr 1 1160567 1740851 (by norm_num) (by norm_num) (sr 1 1740851 2611277 (by norm_num) (by norm_num) (sr 3 2611277 979229 (by norm_num) (by norm_num) (sr 3 979229 367211 (by norm_num) (by norm_num) (sr 1 367211 550817 (by norm_num) (by norm_num) (sr 2 550817 413113 (by norm_num) (by norm_num) (sr 2 413113 309835 (by norm_num) (by norm_num) (sr 1 309835 464753 (by norm_num) (by norm_num) (sr 2 464753 348565 (by norm_num) (by norm_num) (sr 6 348565 16339 (by norm_num) (by norm_num) (B 16339 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))
theorem R101891 : Reach 101891 := (sr 1 101891 152837 (by norm_num) (by norm_num) (sr 4 152837 28657 (by norm_num) (by norm_num) (B 28657 (by norm_num) (by norm_num) (by norm_num))))
theorem R101895 : Reach 101895 := (sr 1 101895 152843 (by norm_num) (by norm_num) (sr 1 152843 229265 (by norm_num) (by norm_num) (sr 2 229265 171949 (by norm_num) (by norm_num) (sr 3 171949 64481 (by norm_num) (by norm_num) (B 64481 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101899 : Reach 101899 := (sr 1 101899 152849 (by norm_num) (by norm_num) (sr 2 152849 114637 (by norm_num) (by norm_num) (sr 3 114637 42989 (by norm_num) (by norm_num) (B 42989 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101903 : Reach 101903 := (sr 1 101903 152855 (by norm_num) (by norm_num) (sr 1 152855 229283 (by norm_num) (by norm_num) (sr 1 229283 343925 (by norm_num) (by norm_num) (sr 5 343925 32243 (by norm_num) (by norm_num) (B 32243 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101907 : Reach 101907 := (sr 1 101907 152861 (by norm_num) (by norm_num) (sr 3 152861 57323 (by norm_num) (by norm_num) (B 57323 (by norm_num) (by norm_num) (by norm_num))))
theorem R101911 : Reach 101911 := (sr 1 101911 152867 (by norm_num) (by norm_num) (sr 1 152867 229301 (by norm_num) (by norm_num) (sr 5 229301 21497 (by norm_num) (by norm_num) (B 21497 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101915 : Reach 101915 := (sr 1 101915 152873 (by norm_num) (by norm_num) (sr 2 152873 114655 (by norm_num) (by norm_num) (sr 1 114655 171983 (by norm_num) (by norm_num) (sr 1 171983 257975 (by norm_num) (by norm_num) (sr 1 257975 386963 (by norm_num) (by norm_num) (sr 1 386963 580445 (by norm_num) (by norm_num) (sr 3 580445 217667 (by norm_num) (by norm_num) (sr 1 217667 326501 (by norm_num) (by norm_num) (sr 4 326501 61219 (by norm_num) (by norm_num) (B 61219 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R101919 : Reach 101919 := (sr 1 101919 152879 (by norm_num) (by norm_num) (sr 1 152879 229319 (by norm_num) (by norm_num) (sr 1 229319 343979 (by norm_num) (by norm_num) (sr 1 343979 515969 (by norm_num) (by norm_num) (sr 2 515969 386977 (by norm_num) (by norm_num) (sr 2 386977 290233 (by norm_num) (by norm_num) (sr 2 290233 217675 (by norm_num) (by norm_num) (sr 1 217675 326513 (by norm_num) (by norm_num) (sr 2 326513 244885 (by norm_num) (by norm_num) (sr 6 244885 11479 (by norm_num) (by norm_num) (B 11479 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R101923 : Reach 101923 := (sr 1 101923 152885 (by norm_num) (by norm_num) (sr 5 152885 14333 (by norm_num) (by norm_num) (B 14333 (by norm_num) (by norm_num) (by norm_num))))
theorem R101927 : Reach 101927 := (sr 1 101927 152891 (by norm_num) (by norm_num) (sr 1 152891 229337 (by norm_num) (by norm_num) (sr 2 229337 172003 (by norm_num) (by norm_num) (sr 1 172003 258005 (by norm_num) (by norm_num) (sr 7 258005 6047 (by norm_num) (by norm_num) (B 6047 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101931 : Reach 101931 := (sr 1 101931 152897 (by norm_num) (by norm_num) (sr 2 152897 114673 (by norm_num) (by norm_num) (sr 2 114673 86005 (by norm_num) (by norm_num) (B 86005 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101935 : Reach 101935 := (sr 1 101935 152903 (by norm_num) (by norm_num) (sr 1 152903 229355 (by norm_num) (by norm_num) (sr 1 229355 344033 (by norm_num) (by norm_num) (sr 2 344033 258025 (by norm_num) (by norm_num) (sr 2 258025 193519 (by norm_num) (by norm_num) (sr 1 193519 290279 (by norm_num) (by norm_num) (sr 1 290279 435419 (by norm_num) (by norm_num) (sr 1 435419 653129 (by norm_num) (by norm_num) (sr 2 653129 489847 (by norm_num) (by norm_num) (sr 1 489847 734771 (by norm_num) (by norm_num) (sr 1 734771 1102157 (by norm_num) (by norm_num) (sr 3 1102157 413309 (by norm_num) (by norm_num) (sr 3 413309 154991 (by norm_num) (by norm_num) (sr 1 154991 232487 (by norm_num) (by norm_num) (sr 1 232487 348731 (by norm_num) (by norm_num) (sr 1 348731 523097 (by norm_num) (by norm_num) (sr 2 523097 392323 (by norm_num) (by norm_num) (sr 1 392323 588485 (by norm_num) (by norm_num) (sr 4 588485 110341 (by norm_num) (by norm_num) (sr 4 110341 20689 (by norm_num) (by norm_num) (B 20689 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))
theorem R101939 : Reach 101939 := (sr 1 101939 152909 (by norm_num) (by norm_num) (sr 3 152909 57341 (by norm_num) (by norm_num) (B 57341 (by norm_num) (by norm_num) (by norm_num))))
theorem R101943 : Reach 101943 := (sr 1 101943 152915 (by norm_num) (by norm_num) (sr 1 152915 229373 (by norm_num) (by norm_num) (sr 3 229373 86015 (by norm_num) (by norm_num) (B 86015 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101947 : Reach 101947 := (sr 1 101947 152921 (by norm_num) (by norm_num) (sr 2 152921 114691 (by norm_num) (by norm_num) (sr 1 114691 172037 (by norm_num) (by norm_num) (sr 4 172037 32257 (by norm_num) (by norm_num) (B 32257 (by norm_num) (by norm_num) (by norm_num))))))
theorem R101951 : Reach 101951 := (sr 1 101951 152927 (by norm_num) (by norm_num) (sr 1 152927 229391 (by norm_num) (by norm_num) (sr 1 229391 344087 (by norm_num) (by norm_num) (sr 1 344087 516131 (by norm_num) (by norm_num) (sr 1 516131 774197 (by norm_num) (by norm_num) (sr 5 774197 72581 (by norm_num) (by norm_num) (B 72581 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R101955 : Reach 101955 := (sr 1 101955 152933 (by norm_num) (by norm_num) (sr 4 152933 28675 (by norm_num) (by norm_num) (B 28675 (by norm_num) (by norm_num) (by norm_num))))
theorem R101959 : Reach 101959 := (sr 1 101959 152939 (by norm_num) (by norm_num) (sr 1 152939 229409 (by norm_num) (by norm_num) (sr 2 229409 172057 (by norm_num) (by norm_num) (sr 2 172057 129043 (by norm_num) (by norm_num) (sr 1 129043 193565 (by norm_num) (by norm_num) (sr 3 193565 72587 (by norm_num) (by norm_num) (B 72587 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R101963 : Reach 101963 := (sr 1 101963 152945 (by norm_num) (by norm_num) (sr 2 152945 114709 (by norm_num) (by norm_num) (sr 6 114709 5377 (by norm_num) (by norm_num) (B 5377 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101967 : Reach 101967 := (sr 1 101967 152951 (by norm_num) (by norm_num) (sr 1 152951 229427 (by norm_num) (by norm_num) (sr 1 229427 344141 (by norm_num) (by norm_num) (sr 3 344141 129053 (by norm_num) (by norm_num) (sr 3 129053 48395 (by norm_num) (by norm_num) (B 48395 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101971 : Reach 101971 := (sr 1 101971 152957 (by norm_num) (by norm_num) (sr 3 152957 57359 (by norm_num) (by norm_num) (B 57359 (by norm_num) (by norm_num) (by norm_num))))
theorem R101975 : Reach 101975 := (sr 1 101975 152963 (by norm_num) (by norm_num) (sr 1 152963 229445 (by norm_num) (by norm_num) (sr 4 229445 43021 (by norm_num) (by norm_num) (B 43021 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101979 : Reach 101979 := (sr 1 101979 152969 (by norm_num) (by norm_num) (sr 2 152969 114727 (by norm_num) (by norm_num) (sr 1 114727 172091 (by norm_num) (by norm_num) (sr 1 172091 258137 (by norm_num) (by norm_num) (sr 2 258137 193603 (by norm_num) (by norm_num) (sr 1 193603 290405 (by norm_num) (by norm_num) (sr 4 290405 54451 (by norm_num) (by norm_num) (B 54451 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R101983 : Reach 101983 := (sr 1 101983 152975 (by norm_num) (by norm_num) (sr 1 152975 229463 (by norm_num) (by norm_num) (sr 1 229463 344195 (by norm_num) (by norm_num) (sr 1 344195 516293 (by norm_num) (by norm_num) (sr 4 516293 96805 (by norm_num) (by norm_num) (B 96805 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R101987 : Reach 101987 := (sr 1 101987 152981 (by norm_num) (by norm_num) (sr 6 152981 7171 (by norm_num) (by norm_num) (B 7171 (by norm_num) (by norm_num) (by norm_num))))
theorem R101991 : Reach 101991 := (sr 1 101991 152987 (by norm_num) (by norm_num) (sr 1 152987 229481 (by norm_num) (by norm_num) (sr 2 229481 172111 (by norm_num) (by norm_num) (sr 1 172111 258167 (by norm_num) (by norm_num) (sr 1 258167 387251 (by norm_num) (by norm_num) (sr 1 387251 580877 (by norm_num) (by norm_num) (sr 3 580877 217829 (by norm_num) (by norm_num) (sr 4 217829 40843 (by norm_num) (by norm_num) (B 40843 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R101995 : Reach 101995 := (sr 1 101995 152993 (by norm_num) (by norm_num) (sr 2 152993 114745 (by norm_num) (by norm_num) (sr 2 114745 86059 (by norm_num) (by norm_num) (B 86059 (by norm_num) (by norm_num) (by norm_num)))))
theorem R101999 : Reach 101999 := (sr 1 101999 152999 (by norm_num) (by norm_num) (sr 1 152999 229499 (by norm_num) (by norm_num) (sr 1 229499 344249 (by norm_num) (by norm_num) (sr 2 344249 258187 (by norm_num) (by norm_num) (sr 1 258187 387281 (by norm_num) (by norm_num) (sr 2 387281 290461 (by norm_num) (by norm_num) (sr 3 290461 108923 (by norm_num) (by norm_num) (sr 1 108923 163385 (by norm_num) (by norm_num) (sr 2 163385 122539 (by norm_num) (by norm_num) (sr 1 122539 183809 (by norm_num) (by norm_num) (sr 2 183809 137857 (by norm_num) (by norm_num) (sr 2 137857 103393 (by norm_num) (by norm_num) (sr 2 103393 77545 (by norm_num) (by norm_num) (B 77545 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R102003 : Reach 102003 := (sr 1 102003 153005 (by norm_num) (by norm_num) (sr 3 153005 57377 (by norm_num) (by norm_num) (B 57377 (by norm_num) (by norm_num) (by norm_num))))
theorem R102007 : Reach 102007 := (sr 1 102007 153011 (by norm_num) (by norm_num) (sr 1 153011 229517 (by norm_num) (by norm_num) (sr 3 229517 86069 (by norm_num) (by norm_num) (B 86069 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102011 : Reach 102011 := (sr 1 102011 153017 (by norm_num) (by norm_num) (sr 2 153017 114763 (by norm_num) (by norm_num) (sr 1 114763 172145 (by norm_num) (by norm_num) (sr 2 172145 129109 (by norm_num) (by norm_num) (sr 8 129109 1513 (by norm_num) (by norm_num) (B 1513 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102015 : Reach 102015 := (sr 1 102015 153023 (by norm_num) (by norm_num) (sr 1 153023 229535 (by norm_num) (by norm_num) (sr 1 229535 344303 (by norm_num) (by norm_num) (sr 1 344303 516455 (by norm_num) (by norm_num) (sr 1 516455 774683 (by norm_num) (by norm_num) (sr 1 774683 1162025 (by norm_num) (by norm_num) (sr 2 1162025 871519 (by norm_num) (by norm_num) (sr 1 871519 1307279 (by norm_num) (by norm_num) (sr 1 1307279 1960919 (by norm_num) (by norm_num) (sr 1 1960919 2941379 (by norm_num) (by norm_num) (sr 1 2941379 4412069 (by norm_num) (by norm_num) (sr 4 4412069 827263 (by norm_num) (by norm_num) (sr 1 827263 1240895 (by norm_num) (by norm_num) (sr 1 1240895 1861343 (by norm_num) (by norm_num) (sr 1 1861343 2792015 (by norm_num) (by norm_num) (sr 1 2792015 4188023 (by norm_num) (by norm_num) (sr 1 4188023 6282035 (by norm_num) (by norm_num) (sr 1 6282035 9423053 (by norm_num) (by norm_num) (sr 3 9423053 3533645 (by norm_num) (by norm_num) (sr 3 3533645 1325117 (by norm_num) (by norm_num) (sr 3 1325117 496919 (by norm_num) (by norm_num) (sr 1 496919 745379 (by norm_num) (by norm_num) (sr 1 745379 1118069 (by norm_num) (by norm_num) (sr 5 1118069 104819 (by norm_num) (by norm_num) (sr 1 104819 157229 (by norm_num) (by norm_num) (sr 3 157229 58961 (by norm_num) (by norm_num) (B 58961 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))
theorem R102019 : Reach 102019 := (sr 1 102019 153029 (by norm_num) (by norm_num) (sr 4 153029 28693 (by norm_num) (by norm_num) (B 28693 (by norm_num) (by norm_num) (by norm_num))))
theorem R102023 : Reach 102023 := (sr 1 102023 153035 (by norm_num) (by norm_num) (sr 1 153035 229553 (by norm_num) (by norm_num) (sr 2 229553 172165 (by norm_num) (by norm_num) (sr 4 172165 32281 (by norm_num) (by norm_num) (B 32281 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102027 : Reach 102027 := (sr 1 102027 153041 (by norm_num) (by norm_num) (sr 2 153041 114781 (by norm_num) (by norm_num) (sr 3 114781 43043 (by norm_num) (by norm_num) (B 43043 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102031 : Reach 102031 := (sr 1 102031 153047 (by norm_num) (by norm_num) (sr 1 153047 229571 (by norm_num) (by norm_num) (sr 1 229571 344357 (by norm_num) (by norm_num) (sr 4 344357 64567 (by norm_num) (by norm_num) (B 64567 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102035 : Reach 102035 := (sr 1 102035 153053 (by norm_num) (by norm_num) (sr 3 153053 57395 (by norm_num) (by norm_num) (B 57395 (by norm_num) (by norm_num) (by norm_num))))
theorem R102039 : Reach 102039 := (sr 1 102039 153059 (by norm_num) (by norm_num) (sr 1 153059 229589 (by norm_num) (by norm_num) (sr 7 229589 5381 (by norm_num) (by norm_num) (B 5381 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102043 : Reach 102043 := (sr 1 102043 153065 (by norm_num) (by norm_num) (sr 2 153065 114799 (by norm_num) (by norm_num) (sr 1 114799 172199 (by norm_num) (by norm_num) (sr 1 172199 258299 (by norm_num) (by norm_num) (sr 1 258299 387449 (by norm_num) (by norm_num) (sr 2 387449 290587 (by norm_num) (by norm_num) (sr 1 290587 435881 (by norm_num) (by norm_num) (sr 2 435881 326911 (by norm_num) (by norm_num) (sr 1 326911 490367 (by norm_num) (by norm_num) (sr 1 490367 735551 (by norm_num) (by norm_num) (sr 1 735551 1103327 (by norm_num) (by norm_num) (sr 1 1103327 1654991 (by norm_num) (by norm_num) (sr 1 1654991 2482487 (by norm_num) (by norm_num) (sr 1 2482487 3723731 (by norm_num) (by norm_num) (sr 1 3723731 5585597 (by norm_num) (by norm_num) (sr 3 5585597 2094599 (by norm_num) (by norm_num) (sr 1 2094599 3141899 (by norm_num) (by norm_num) (sr 1 3141899 4712849 (by norm_num) (by norm_num) (sr 2 4712849 3534637 (by norm_num) (by norm_num) (sr 3 3534637 1325489 (by norm_num) (by norm_num) (sr 2 1325489 994117 (by norm_num) (by norm_num) (sr 4 994117 186397 (by norm_num) (by norm_num) (sr 3 186397 69899 (by norm_num) (by norm_num) (B 69899 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))
theorem R102047 : Reach 102047 := (sr 1 102047 153071 (by norm_num) (by norm_num) (sr 1 153071 229607 (by norm_num) (by norm_num) (sr 1 229607 344411 (by norm_num) (by norm_num) (sr 1 344411 516617 (by norm_num) (by norm_num) (sr 2 516617 387463 (by norm_num) (by norm_num) (sr 1 387463 581195 (by norm_num) (by norm_num) (sr 1 581195 871793 (by norm_num) (by norm_num) (sr 2 871793 653845 (by norm_num) (by norm_num) (sr 6 653845 30649 (by norm_num) (by norm_num) (B 30649 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R102051 : Reach 102051 := (sr 1 102051 153077 (by norm_num) (by norm_num) (sr 5 153077 14351 (by norm_num) (by norm_num) (B 14351 (by norm_num) (by norm_num) (by norm_num))))
theorem R102055 : Reach 102055 := (sr 1 102055 153083 (by norm_num) (by norm_num) (sr 1 153083 229625 (by norm_num) (by norm_num) (sr 2 229625 172219 (by norm_num) (by norm_num) (sr 1 172219 258329 (by norm_num) (by norm_num) (sr 2 258329 193747 (by norm_num) (by norm_num) (sr 1 193747 290621 (by norm_num) (by norm_num) (sr 3 290621 108983 (by norm_num) (by norm_num) (sr 1 108983 163475 (by norm_num) (by norm_num) (sr 1 163475 245213 (by norm_num) (by norm_num) (sr 3 245213 91955 (by norm_num) (by norm_num) (B 91955 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R102059 : Reach 102059 := (sr 1 102059 153089 (by norm_num) (by norm_num) (sr 2 153089 114817 (by norm_num) (by norm_num) (sr 2 114817 86113 (by norm_num) (by norm_num) (B 86113 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102063 : Reach 102063 := (sr 1 102063 153095 (by norm_num) (by norm_num) (sr 1 153095 229643 (by norm_num) (by norm_num) (sr 1 229643 344465 (by norm_num) (by norm_num) (sr 2 344465 258349 (by norm_num) (by norm_num) (sr 3 258349 96881 (by norm_num) (by norm_num) (B 96881 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102067 : Reach 102067 := (sr 1 102067 153101 (by norm_num) (by norm_num) (sr 3 153101 57413 (by norm_num) (by norm_num) (B 57413 (by norm_num) (by norm_num) (by norm_num))))
theorem R102071 : Reach 102071 := (sr 1 102071 153107 (by norm_num) (by norm_num) (sr 1 153107 229661 (by norm_num) (by norm_num) (sr 3 229661 86123 (by norm_num) (by norm_num) (B 86123 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102075 : Reach 102075 := (sr 1 102075 153113 (by norm_num) (by norm_num) (sr 2 153113 114835 (by norm_num) (by norm_num) (sr 1 114835 172253 (by norm_num) (by norm_num) (sr 3 172253 64595 (by norm_num) (by norm_num) (B 64595 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102079 : Reach 102079 := (sr 1 102079 153119 (by norm_num) (by norm_num) (sr 1 153119 229679 (by norm_num) (by norm_num) (sr 1 229679 344519 (by norm_num) (by norm_num) (sr 1 344519 516779 (by norm_num) (by norm_num) (sr 1 516779 775169 (by norm_num) (by norm_num) (sr 2 775169 581377 (by norm_num) (by norm_num) (sr 2 581377 436033 (by norm_num) (by norm_num) (sr 2 436033 327025 (by norm_num) (by norm_num) (sr 2 327025 245269 (by norm_num) (by norm_num) (sr 6 245269 11497 (by norm_num) (by norm_num) (B 11497 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R102083 : Reach 102083 := (sr 1 102083 153125 (by norm_num) (by norm_num) (sr 4 153125 28711 (by norm_num) (by norm_num) (B 28711 (by norm_num) (by norm_num) (by norm_num))))
theorem R102087 : Reach 102087 := (sr 1 102087 153131 (by norm_num) (by norm_num) (sr 1 153131 229697 (by norm_num) (by norm_num) (sr 2 229697 172273 (by norm_num) (by norm_num) (sr 2 172273 129205 (by norm_num) (by norm_num) (sr 5 129205 12113 (by norm_num) (by norm_num) (B 12113 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102091 : Reach 102091 := (sr 1 102091 153137 (by norm_num) (by norm_num) (sr 2 153137 114853 (by norm_num) (by norm_num) (sr 4 114853 21535 (by norm_num) (by norm_num) (B 21535 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102095 : Reach 102095 := (sr 1 102095 153143 (by norm_num) (by norm_num) (sr 1 153143 229715 (by norm_num) (by norm_num) (sr 1 229715 344573 (by norm_num) (by norm_num) (sr 3 344573 129215 (by norm_num) (by norm_num) (sr 1 129215 193823 (by norm_num) (by norm_num) (sr 1 193823 290735 (by norm_num) (by norm_num) (sr 1 290735 436103 (by norm_num) (by norm_num) (sr 1 436103 654155 (by norm_num) (by norm_num) (sr 1 654155 981233 (by norm_num) (by norm_num) (sr 2 981233 735925 (by norm_num) (by norm_num) (sr 5 735925 68993 (by norm_num) (by norm_num) (B 68993 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R102099 : Reach 102099 := (sr 1 102099 153149 (by norm_num) (by norm_num) (sr 3 153149 57431 (by norm_num) (by norm_num) (B 57431 (by norm_num) (by norm_num) (by norm_num))))
theorem R102103 : Reach 102103 := (sr 1 102103 153155 (by norm_num) (by norm_num) (sr 1 153155 229733 (by norm_num) (by norm_num) (sr 4 229733 43075 (by norm_num) (by norm_num) (B 43075 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102107 : Reach 102107 := (sr 1 102107 153161 (by norm_num) (by norm_num) (sr 2 153161 114871 (by norm_num) (by norm_num) (sr 1 114871 172307 (by norm_num) (by norm_num) (sr 1 172307 258461 (by norm_num) (by norm_num) (sr 3 258461 96923 (by norm_num) (by norm_num) (B 96923 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102111 : Reach 102111 := (sr 1 102111 153167 (by norm_num) (by norm_num) (sr 1 153167 229751 (by norm_num) (by norm_num) (sr 1 229751 344627 (by norm_num) (by norm_num) (sr 1 344627 516941 (by norm_num) (by norm_num) (sr 3 516941 193853 (by norm_num) (by norm_num) (sr 3 193853 72695 (by norm_num) (by norm_num) (B 72695 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R102115 : Reach 102115 := (sr 1 102115 153173 (by norm_num) (by norm_num) (sr 8 153173 1795 (by norm_num) (by norm_num) (B 1795 (by norm_num) (by norm_num) (by norm_num))))
theorem R102119 : Reach 102119 := (sr 1 102119 153179 (by norm_num) (by norm_num) (sr 1 153179 229769 (by norm_num) (by norm_num) (sr 2 229769 172327 (by norm_num) (by norm_num) (sr 1 172327 258491 (by norm_num) (by norm_num) (sr 1 258491 387737 (by norm_num) (by norm_num) (sr 2 387737 290803 (by norm_num) (by norm_num) (sr 1 290803 436205 (by norm_num) (by norm_num) (sr 3 436205 163577 (by norm_num) (by norm_num) (sr 2 163577 122683 (by norm_num) (by norm_num) (sr 1 122683 184025 (by norm_num) (by norm_num) (sr 2 184025 138019 (by norm_num) (by norm_num) (sr 1 138019 207029 (by norm_num) (by norm_num) (sr 5 207029 19409 (by norm_num) (by norm_num) (B 19409 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R102123 : Reach 102123 := (sr 1 102123 153185 (by norm_num) (by norm_num) (sr 2 153185 114889 (by norm_num) (by norm_num) (sr 2 114889 86167 (by norm_num) (by norm_num) (B 86167 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102127 : Reach 102127 := (sr 1 102127 153191 (by norm_num) (by norm_num) (sr 1 153191 229787 (by norm_num) (by norm_num) (sr 1 229787 344681 (by norm_num) (by norm_num) (sr 2 344681 258511 (by norm_num) (by norm_num) (sr 1 258511 387767 (by norm_num) (by norm_num) (sr 1 387767 581651 (by norm_num) (by norm_num) (sr 1 581651 872477 (by norm_num) (by norm_num) (sr 3 872477 327179 (by norm_num) (by norm_num) (sr 1 327179 490769 (by norm_num) (by norm_num) (sr 2 490769 368077 (by norm_num) (by norm_num) (sr 3 368077 138029 (by norm_num) (by norm_num) (sr 3 138029 51761 (by norm_num) (by norm_num) (B 51761 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R102131 : Reach 102131 := (sr 1 102131 153197 (by norm_num) (by norm_num) (sr 3 153197 57449 (by norm_num) (by norm_num) (B 57449 (by norm_num) (by norm_num) (by norm_num))))
theorem R102135 : Reach 102135 := (sr 1 102135 153203 (by norm_num) (by norm_num) (sr 1 153203 229805 (by norm_num) (by norm_num) (sr 3 229805 86177 (by norm_num) (by norm_num) (B 86177 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102139 : Reach 102139 := (sr 1 102139 153209 (by norm_num) (by norm_num) (sr 2 153209 114907 (by norm_num) (by norm_num) (sr 1 114907 172361 (by norm_num) (by norm_num) (sr 2 172361 129271 (by norm_num) (by norm_num) (sr 1 129271 193907 (by norm_num) (by norm_num) (sr 1 193907 290861 (by norm_num) (by norm_num) (sr 3 290861 109073 (by norm_num) (by norm_num) (sr 2 109073 81805 (by norm_num) (by norm_num) (B 81805 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R102143 : Reach 102143 := (sr 1 102143 153215 (by norm_num) (by norm_num) (sr 1 153215 229823 (by norm_num) (by norm_num) (sr 1 229823 344735 (by norm_num) (by norm_num) (sr 1 344735 517103 (by norm_num) (by norm_num) (sr 1 517103 775655 (by norm_num) (by norm_num) (sr 1 775655 1163483 (by norm_num) (by norm_num) (sr 1 1163483 1745225 (by norm_num) (by norm_num) (sr 2 1745225 1308919 (by norm_num) (by norm_num) (sr 1 1308919 1963379 (by norm_num) (by norm_num) (sr 1 1963379 2945069 (by norm_num) (by norm_num) (sr 3 2945069 1104401 (by norm_num) (by norm_num) (sr 2 1104401 828301 (by norm_num) (by norm_num) (sr 3 828301 310613 (by norm_num) (by norm_num) (sr 11 310613 455 (by norm_num) (by norm_num) (B 455 (by norm_num) (by norm_num) (by norm_num))))))))))))))))
theorem R102147 : Reach 102147 := (sr 1 102147 153221 (by norm_num) (by norm_num) (sr 4 153221 28729 (by norm_num) (by norm_num) (B 28729 (by norm_num) (by norm_num) (by norm_num))))
theorem R102151 : Reach 102151 := (sr 1 102151 153227 (by norm_num) (by norm_num) (sr 1 153227 229841 (by norm_num) (by norm_num) (sr 2 229841 172381 (by norm_num) (by norm_num) (sr 3 172381 64643 (by norm_num) (by norm_num) (B 64643 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102155 : Reach 102155 := (sr 1 102155 153233 (by norm_num) (by norm_num) (sr 2 153233 114925 (by norm_num) (by norm_num) (sr 3 114925 43097 (by norm_num) (by norm_num) (B 43097 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102159 : Reach 102159 := (sr 1 102159 153239 (by norm_num) (by norm_num) (sr 1 153239 229859 (by norm_num) (by norm_num) (sr 1 229859 344789 (by norm_num) (by norm_num) (sr 7 344789 8081 (by norm_num) (by norm_num) (B 8081 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102163 : Reach 102163 := (sr 1 102163 153245 (by norm_num) (by norm_num) (sr 3 153245 57467 (by norm_num) (by norm_num) (B 57467 (by norm_num) (by norm_num) (by norm_num))))
theorem R102167 : Reach 102167 := (sr 1 102167 153251 (by norm_num) (by norm_num) (sr 1 153251 229877 (by norm_num) (by norm_num) (sr 5 229877 21551 (by norm_num) (by norm_num) (B 21551 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102171 : Reach 102171 := (sr 1 102171 153257 (by norm_num) (by norm_num) (sr 2 153257 114943 (by norm_num) (by norm_num) (sr 1 114943 172415 (by norm_num) (by norm_num) (sr 1 172415 258623 (by norm_num) (by norm_num) (sr 1 258623 387935 (by norm_num) (by norm_num) (sr 1 387935 581903 (by norm_num) (by norm_num) (sr 1 581903 872855 (by norm_num) (by norm_num) (sr 1 872855 1309283 (by norm_num) (by norm_num) (sr 1 1309283 1963925 (by norm_num) (by norm_num) (sr 6 1963925 92059 (by norm_num) (by norm_num) (B 92059 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R102175 : Reach 102175 := (sr 1 102175 153263 (by norm_num) (by norm_num) (sr 1 153263 229895 (by norm_num) (by norm_num) (sr 1 229895 344843 (by norm_num) (by norm_num) (sr 1 344843 517265 (by norm_num) (by norm_num) (sr 2 517265 387949 (by norm_num) (by norm_num) (sr 3 387949 145481 (by norm_num) (by norm_num) (sr 2 145481 109111 (by norm_num) (by norm_num) (sr 1 109111 163667 (by norm_num) (by norm_num) (sr 1 163667 245501 (by norm_num) (by norm_num) (sr 3 245501 92063 (by norm_num) (by norm_num) (B 92063 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R102179 : Reach 102179 := (sr 1 102179 153269 (by norm_num) (by norm_num) (sr 5 153269 14369 (by norm_num) (by norm_num) (B 14369 (by norm_num) (by norm_num) (by norm_num))))
theorem R102183 : Reach 102183 := (sr 1 102183 153275 (by norm_num) (by norm_num) (sr 1 153275 229913 (by norm_num) (by norm_num) (sr 2 229913 172435 (by norm_num) (by norm_num) (sr 1 172435 258653 (by norm_num) (by norm_num) (sr 3 258653 96995 (by norm_num) (by norm_num) (B 96995 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102187 : Reach 102187 := (sr 1 102187 153281 (by norm_num) (by norm_num) (sr 2 153281 114961 (by norm_num) (by norm_num) (sr 2 114961 86221 (by norm_num) (by norm_num) (B 86221 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102191 : Reach 102191 := (sr 1 102191 153287 (by norm_num) (by norm_num) (sr 1 153287 229931 (by norm_num) (by norm_num) (sr 1 229931 344897 (by norm_num) (by norm_num) (sr 2 344897 258673 (by norm_num) (by norm_num) (sr 2 258673 194005 (by norm_num) (by norm_num) (sr 7 194005 4547 (by norm_num) (by norm_num) (B 4547 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R102195 : Reach 102195 := (sr 1 102195 153293 (by norm_num) (by norm_num) (sr 3 153293 57485 (by norm_num) (by norm_num) (B 57485 (by norm_num) (by norm_num) (by norm_num))))
theorem R102199 : Reach 102199 := (sr 1 102199 153299 (by norm_num) (by norm_num) (sr 1 153299 229949 (by norm_num) (by norm_num) (sr 3 229949 86231 (by norm_num) (by norm_num) (B 86231 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102203 : Reach 102203 := (sr 1 102203 153305 (by norm_num) (by norm_num) (sr 2 153305 114979 (by norm_num) (by norm_num) (sr 1 114979 172469 (by norm_num) (by norm_num) (sr 5 172469 16169 (by norm_num) (by norm_num) (B 16169 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102207 : Reach 102207 := (sr 1 102207 153311 (by norm_num) (by norm_num) (sr 1 153311 229967 (by norm_num) (by norm_num) (sr 1 229967 344951 (by norm_num) (by norm_num) (sr 1 344951 517427 (by norm_num) (by norm_num) (sr 1 517427 776141 (by norm_num) (by norm_num) (sr 3 776141 291053 (by norm_num) (by norm_num) (sr 3 291053 109145 (by norm_num) (by norm_num) (sr 2 109145 81859 (by norm_num) (by norm_num) (B 81859 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R102211 : Reach 102211 := (sr 1 102211 153317 (by norm_num) (by norm_num) (sr 4 153317 28747 (by norm_num) (by norm_num) (B 28747 (by norm_num) (by norm_num) (by norm_num))))
theorem R102215 : Reach 102215 := (sr 1 102215 153323 (by norm_num) (by norm_num) (sr 1 153323 229985 (by norm_num) (by norm_num) (sr 2 229985 172489 (by norm_num) (by norm_num) (sr 2 172489 129367 (by norm_num) (by norm_num) (sr 1 129367 194051 (by norm_num) (by norm_num) (sr 1 194051 291077 (by norm_num) (by norm_num) (sr 4 291077 54577 (by norm_num) (by norm_num) (B 54577 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R102219 : Reach 102219 := (sr 1 102219 153329 (by norm_num) (by norm_num) (sr 2 153329 114997 (by norm_num) (by norm_num) (sr 5 114997 10781 (by norm_num) (by norm_num) (B 10781 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102223 : Reach 102223 := (sr 1 102223 153335 (by norm_num) (by norm_num) (sr 1 153335 230003 (by norm_num) (by norm_num) (sr 1 230003 345005 (by norm_num) (by norm_num) (sr 3 345005 129377 (by norm_num) (by norm_num) (sr 2 129377 97033 (by norm_num) (by norm_num) (B 97033 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102227 : Reach 102227 := (sr 1 102227 153341 (by norm_num) (by norm_num) (sr 3 153341 57503 (by norm_num) (by norm_num) (B 57503 (by norm_num) (by norm_num) (by norm_num))))
theorem R102231 : Reach 102231 := (sr 1 102231 153347 (by norm_num) (by norm_num) (sr 1 153347 230021 (by norm_num) (by norm_num) (sr 4 230021 43129 (by norm_num) (by norm_num) (B 43129 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102235 : Reach 102235 := (sr 1 102235 153353 (by norm_num) (by norm_num) (sr 2 153353 115015 (by norm_num) (by norm_num) (sr 1 115015 172523 (by norm_num) (by norm_num) (sr 1 172523 258785 (by norm_num) (by norm_num) (sr 2 258785 194089 (by norm_num) (by norm_num) (sr 2 194089 145567 (by norm_num) (by norm_num) (sr 1 145567 218351 (by norm_num) (by norm_num) (sr 1 218351 327527 (by norm_num) (by norm_num) (sr 1 327527 491291 (by norm_num) (by norm_num) (sr 1 491291 736937 (by norm_num) (by norm_num) (sr 2 736937 552703 (by norm_num) (by norm_num) (sr 1 552703 829055 (by norm_num) (by norm_num) (sr 1 829055 1243583 (by norm_num) (by norm_num) (sr 1 1243583 1865375 (by norm_num) (by norm_num) (sr 1 1865375 2798063 (by norm_num) (by norm_num) (sr 1 2798063 4197095 (by norm_num) (by norm_num) (sr 1 4197095 6295643 (by norm_num) (by norm_num) (sr 1 6295643 9443465 (by norm_num) (by norm_num) (sr 2 9443465 7082599 (by norm_num) (by norm_num) (sr 1 7082599 10623899 (by norm_num) (by norm_num) (sr 1 10623899 15935849 (by norm_num) (by norm_num) (sr 2 15935849 11951887 (by norm_num) (by norm_num) (sr 1 11951887 17927831 (by norm_num) (by norm_num) (sr 1 17927831 26891747 (by norm_num) (by norm_num) (sr 1 26891747 40337621 (by norm_num) (by norm_num) (sr 7 40337621 945413 (by norm_num) (by norm_num) (sr 4 945413 177265 (by norm_num) (by norm_num) (sr 2 177265 132949 (by norm_num) (by norm_num) (sr 9 132949 779 (by norm_num) (by norm_num) (B 779 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))
theorem R102239 : Reach 102239 := (sr 1 102239 153359 (by norm_num) (by norm_num) (sr 1 153359 230039 (by norm_num) (by norm_num) (sr 1 230039 345059 (by norm_num) (by norm_num) (sr 1 345059 517589 (by norm_num) (by norm_num) (sr 7 517589 12131 (by norm_num) (by norm_num) (B 12131 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102243 : Reach 102243 := (sr 1 102243 153365 (by norm_num) (by norm_num) (sr 6 153365 7189 (by norm_num) (by norm_num) (B 7189 (by norm_num) (by norm_num) (by norm_num))))
theorem R102247 : Reach 102247 := (sr 1 102247 153371 (by norm_num) (by norm_num) (sr 1 153371 230057 (by norm_num) (by norm_num) (sr 2 230057 172543 (by norm_num) (by norm_num) (sr 1 172543 258815 (by norm_num) (by norm_num) (sr 1 258815 388223 (by norm_num) (by norm_num) (sr 1 388223 582335 (by norm_num) (by norm_num) (sr 1 582335 873503 (by norm_num) (by norm_num) (sr 1 873503 1310255 (by norm_num) (by norm_num) (sr 1 1310255 1965383 (by norm_num) (by norm_num) (sr 1 1965383 2948075 (by norm_num) (by norm_num) (sr 1 2948075 4422113 (by norm_num) (by norm_num) (sr 2 4422113 3316585 (by norm_num) (by norm_num) (sr 2 3316585 2487439 (by norm_num) (by norm_num) (sr 1 2487439 3731159 (by norm_num) (by norm_num) (sr 1 3731159 5596739 (by norm_num) (by norm_num) (sr 1 5596739 8395109 (by norm_num) (by norm_num) (sr 4 8395109 1574083 (by norm_num) (by norm_num) (sr 1 1574083 2361125 (by norm_num) (by norm_num) (sr 4 2361125 442711 (by norm_num) (by norm_num) (sr 1 442711 664067 (by norm_num) (by norm_num) (sr 1 664067 996101 (by norm_num) (by norm_num) (sr 4 996101 186769 (by norm_num) (by norm_num) (sr 2 186769 140077 (by norm_num) (by norm_num) (sr 3 140077 52529 (by norm_num) (by norm_num) (B 52529 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))
theorem R102251 : Reach 102251 := (sr 1 102251 153377 (by norm_num) (by norm_num) (sr 2 153377 115033 (by norm_num) (by norm_num) (sr 2 115033 86275 (by norm_num) (by norm_num) (B 86275 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102255 : Reach 102255 := (sr 1 102255 153383 (by norm_num) (by norm_num) (sr 1 153383 230075 (by norm_num) (by norm_num) (sr 1 230075 345113 (by norm_num) (by norm_num) (sr 2 345113 258835 (by norm_num) (by norm_num) (sr 1 258835 388253 (by norm_num) (by norm_num) (sr 3 388253 145595 (by norm_num) (by norm_num) (sr 1 145595 218393 (by norm_num) (by norm_num) (sr 2 218393 163795 (by norm_num) (by norm_num) (sr 1 163795 245693 (by norm_num) (by norm_num) (sr 3 245693 92135 (by norm_num) (by norm_num) (B 92135 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R102259 : Reach 102259 := (sr 1 102259 153389 (by norm_num) (by norm_num) (sr 3 153389 57521 (by norm_num) (by norm_num) (B 57521 (by norm_num) (by norm_num) (by norm_num))))
theorem R102263 : Reach 102263 := (sr 1 102263 153395 (by norm_num) (by norm_num) (sr 1 153395 230093 (by norm_num) (by norm_num) (sr 3 230093 86285 (by norm_num) (by norm_num) (B 86285 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102267 : Reach 102267 := (sr 1 102267 153401 (by norm_num) (by norm_num) (sr 2 153401 115051 (by norm_num) (by norm_num) (sr 1 115051 172577 (by norm_num) (by norm_num) (sr 2 172577 129433 (by norm_num) (by norm_num) (sr 2 129433 97075 (by norm_num) (by norm_num) (B 97075 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102271 : Reach 102271 := (sr 1 102271 153407 (by norm_num) (by norm_num) (sr 1 153407 230111 (by norm_num) (by norm_num) (sr 1 230111 345167 (by norm_num) (by norm_num) (sr 1 345167 517751 (by norm_num) (by norm_num) (sr 1 517751 776627 (by norm_num) (by norm_num) (sr 1 776627 1164941 (by norm_num) (by norm_num) (sr 3 1164941 436853 (by norm_num) (by norm_num) (sr 5 436853 40955 (by norm_num) (by norm_num) (B 40955 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R102275 : Reach 102275 := (sr 1 102275 153413 (by norm_num) (by norm_num) (sr 4 153413 28765 (by norm_num) (by norm_num) (B 28765 (by norm_num) (by norm_num) (by norm_num))))
theorem R102279 : Reach 102279 := (sr 1 102279 153419 (by norm_num) (by norm_num) (sr 1 153419 230129 (by norm_num) (by norm_num) (sr 2 230129 172597 (by norm_num) (by norm_num) (sr 5 172597 16181 (by norm_num) (by norm_num) (B 16181 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102283 : Reach 102283 := (sr 1 102283 153425 (by norm_num) (by norm_num) (sr 2 153425 115069 (by norm_num) (by norm_num) (sr 3 115069 43151 (by norm_num) (by norm_num) (B 43151 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102287 : Reach 102287 := (sr 1 102287 153431 (by norm_num) (by norm_num) (sr 1 153431 230147 (by norm_num) (by norm_num) (sr 1 230147 345221 (by norm_num) (by norm_num) (sr 4 345221 64729 (by norm_num) (by norm_num) (B 64729 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102291 : Reach 102291 := (sr 1 102291 153437 (by norm_num) (by norm_num) (sr 3 153437 57539 (by norm_num) (by norm_num) (B 57539 (by norm_num) (by norm_num) (by norm_num))))
theorem R102295 : Reach 102295 := (sr 1 102295 153443 (by norm_num) (by norm_num) (sr 1 153443 230165 (by norm_num) (by norm_num) (sr 6 230165 10789 (by norm_num) (by norm_num) (B 10789 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102299 : Reach 102299 := (sr 1 102299 153449 (by norm_num) (by norm_num) (sr 2 153449 115087 (by norm_num) (by norm_num) (sr 1 115087 172631 (by norm_num) (by norm_num) (sr 1 172631 258947 (by norm_num) (by norm_num) (sr 1 258947 388421 (by norm_num) (by norm_num) (sr 4 388421 72829 (by norm_num) (by norm_num) (B 72829 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R102303 : Reach 102303 := (sr 1 102303 153455 (by norm_num) (by norm_num) (sr 1 153455 230183 (by norm_num) (by norm_num) (sr 1 230183 345275 (by norm_num) (by norm_num) (sr 1 345275 517913 (by norm_num) (by norm_num) (sr 2 517913 388435 (by norm_num) (by norm_num) (sr 1 388435 582653 (by norm_num) (by norm_num) (sr 3 582653 218495 (by norm_num) (by norm_num) (sr 1 218495 327743 (by norm_num) (by norm_num) (sr 1 327743 491615 (by norm_num) (by norm_num) (sr 1 491615 737423 (by norm_num) (by norm_num) (sr 1 737423 1106135 (by norm_num) (by norm_num) (sr 1 1106135 1659203 (by norm_num) (by norm_num) (sr 1 1659203 2488805 (by norm_num) (by norm_num) (sr 4 2488805 466651 (by norm_num) (by norm_num) (sr 1 466651 699977 (by norm_num) (by norm_num) (sr 2 699977 524983 (by norm_num) (by norm_num) (sr 1 524983 787475 (by norm_num) (by norm_num) (sr 1 787475 1181213 (by norm_num) (by norm_num) (sr 3 1181213 442955 (by norm_num) (by norm_num) (sr 1 442955 664433 (by norm_num) (by norm_num) (sr 2 664433 498325 (by norm_num) (by norm_num) (sr 6 498325 23359 (by norm_num) (by norm_num) (B 23359 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R102307 : Reach 102307 := (sr 1 102307 153461 (by norm_num) (by norm_num) (sr 5 153461 14387 (by norm_num) (by norm_num) (B 14387 (by norm_num) (by norm_num) (by norm_num))))
theorem R102311 : Reach 102311 := (sr 1 102311 153467 (by norm_num) (by norm_num) (sr 1 153467 230201 (by norm_num) (by norm_num) (sr 2 230201 172651 (by norm_num) (by norm_num) (sr 1 172651 258977 (by norm_num) (by norm_num) (sr 2 258977 194233 (by norm_num) (by norm_num) (sr 2 194233 145675 (by norm_num) (by norm_num) (sr 1 145675 218513 (by norm_num) (by norm_num) (sr 2 218513 163885 (by norm_num) (by norm_num) (sr 3 163885 61457 (by norm_num) (by norm_num) (B 61457 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R102315 : Reach 102315 := (sr 1 102315 153473 (by norm_num) (by norm_num) (sr 2 153473 115105 (by norm_num) (by norm_num) (sr 2 115105 86329 (by norm_num) (by norm_num) (B 86329 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102319 : Reach 102319 := (sr 1 102319 153479 (by norm_num) (by norm_num) (sr 1 153479 230219 (by norm_num) (by norm_num) (sr 1 230219 345329 (by norm_num) (by norm_num) (sr 2 345329 258997 (by norm_num) (by norm_num) (sr 5 258997 24281 (by norm_num) (by norm_num) (B 24281 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102323 : Reach 102323 := (sr 1 102323 153485 (by norm_num) (by norm_num) (sr 3 153485 57557 (by norm_num) (by norm_num) (B 57557 (by norm_num) (by norm_num) (by norm_num))))
theorem R102327 : Reach 102327 := (sr 1 102327 153491 (by norm_num) (by norm_num) (sr 1 153491 230237 (by norm_num) (by norm_num) (sr 3 230237 86339 (by norm_num) (by norm_num) (B 86339 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102331 : Reach 102331 := (sr 1 102331 153497 (by norm_num) (by norm_num) (sr 2 153497 115123 (by norm_num) (by norm_num) (sr 1 115123 172685 (by norm_num) (by norm_num) (sr 3 172685 64757 (by norm_num) (by norm_num) (B 64757 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102335 : Reach 102335 := (sr 1 102335 153503 (by norm_num) (by norm_num) (sr 1 153503 230255 (by norm_num) (by norm_num) (sr 1 230255 345383 (by norm_num) (by norm_num) (sr 1 345383 518075 (by norm_num) (by norm_num) (sr 1 518075 777113 (by norm_num) (by norm_num) (sr 2 777113 582835 (by norm_num) (by norm_num) (sr 1 582835 874253 (by norm_num) (by norm_num) (sr 3 874253 327845 (by norm_num) (by norm_num) (sr 4 327845 61471 (by norm_num) (by norm_num) (B 61471 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R102339 : Reach 102339 := (sr 1 102339 153509 (by norm_num) (by norm_num) (sr 4 153509 28783 (by norm_num) (by norm_num) (B 28783 (by norm_num) (by norm_num) (by norm_num))))
theorem R102343 : Reach 102343 := (sr 1 102343 153515 (by norm_num) (by norm_num) (sr 1 153515 230273 (by norm_num) (by norm_num) (sr 2 230273 172705 (by norm_num) (by norm_num) (sr 2 172705 129529 (by norm_num) (by norm_num) (sr 2 129529 97147 (by norm_num) (by norm_num) (B 97147 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102347 : Reach 102347 := (sr 1 102347 153521 (by norm_num) (by norm_num) (sr 2 153521 115141 (by norm_num) (by norm_num) (sr 4 115141 21589 (by norm_num) (by norm_num) (B 21589 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102351 : Reach 102351 := (sr 1 102351 153527 (by norm_num) (by norm_num) (sr 1 153527 230291 (by norm_num) (by norm_num) (sr 1 230291 345437 (by norm_num) (by norm_num) (sr 3 345437 129539 (by norm_num) (by norm_num) (sr 1 129539 194309 (by norm_num) (by norm_num) (sr 4 194309 36433 (by norm_num) (by norm_num) (B 36433 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R102355 : Reach 102355 := (sr 1 102355 153533 (by norm_num) (by norm_num) (sr 3 153533 57575 (by norm_num) (by norm_num) (B 57575 (by norm_num) (by norm_num) (by norm_num))))
theorem R102359 : Reach 102359 := (sr 1 102359 153539 (by norm_num) (by norm_num) (sr 1 153539 230309 (by norm_num) (by norm_num) (sr 4 230309 43183 (by norm_num) (by norm_num) (B 43183 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102363 : Reach 102363 := (sr 1 102363 153545 (by norm_num) (by norm_num) (sr 2 153545 115159 (by norm_num) (by norm_num) (sr 1 115159 172739 (by norm_num) (by norm_num) (sr 1 172739 259109 (by norm_num) (by norm_num) (sr 4 259109 48583 (by norm_num) (by norm_num) (B 48583 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102367 : Reach 102367 := (sr 1 102367 153551 (by norm_num) (by norm_num) (sr 1 153551 230327 (by norm_num) (by norm_num) (sr 1 230327 345491 (by norm_num) (by norm_num) (sr 1 345491 518237 (by norm_num) (by norm_num) (sr 3 518237 194339 (by norm_num) (by norm_num) (sr 1 194339 291509 (by norm_num) (by norm_num) (sr 5 291509 27329 (by norm_num) (by norm_num) (B 27329 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R102371 : Reach 102371 := (sr 1 102371 153557 (by norm_num) (by norm_num) (sr 7 153557 3599 (by norm_num) (by norm_num) (B 3599 (by norm_num) (by norm_num) (by norm_num))))
theorem R102375 : Reach 102375 := (sr 1 102375 153563 (by norm_num) (by norm_num) (sr 1 153563 230345 (by norm_num) (by norm_num) (sr 2 230345 172759 (by norm_num) (by norm_num) (sr 1 172759 259139 (by norm_num) (by norm_num) (sr 1 259139 388709 (by norm_num) (by norm_num) (sr 4 388709 72883 (by norm_num) (by norm_num) (B 72883 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R102379 : Reach 102379 := (sr 1 102379 153569 (by norm_num) (by norm_num) (sr 2 153569 115177 (by norm_num) (by norm_num) (sr 2 115177 86383 (by norm_num) (by norm_num) (B 86383 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102383 : Reach 102383 := (sr 1 102383 153575 (by norm_num) (by norm_num) (sr 1 153575 230363 (by norm_num) (by norm_num) (sr 1 230363 345545 (by norm_num) (by norm_num) (sr 2 345545 259159 (by norm_num) (by norm_num) (sr 1 259159 388739 (by norm_num) (by norm_num) (sr 1 388739 583109 (by norm_num) (by norm_num) (sr 4 583109 109333 (by norm_num) (by norm_num) (sr 6 109333 5125 (by norm_num) (by norm_num) (B 5125 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R102387 : Reach 102387 := (sr 1 102387 153581 (by norm_num) (by norm_num) (sr 3 153581 57593 (by norm_num) (by norm_num) (B 57593 (by norm_num) (by norm_num) (by norm_num))))
theorem R102391 : Reach 102391 := (sr 1 102391 153587 (by norm_num) (by norm_num) (sr 1 153587 230381 (by norm_num) (by norm_num) (sr 3 230381 86393 (by norm_num) (by norm_num) (B 86393 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102395 : Reach 102395 := (sr 1 102395 153593 (by norm_num) (by norm_num) (sr 2 153593 115195 (by norm_num) (by norm_num) (sr 1 115195 172793 (by norm_num) (by norm_num) (sr 2 172793 129595 (by norm_num) (by norm_num) (sr 1 129595 194393 (by norm_num) (by norm_num) (sr 2 194393 145795 (by norm_num) (by norm_num) (sr 1 145795 218693 (by norm_num) (by norm_num) (sr 4 218693 41005 (by norm_num) (by norm_num) (B 41005 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R102399 : Reach 102399 := (sr 1 102399 153599 (by norm_num) (by norm_num) (sr 1 153599 230399 (by norm_num) (by norm_num) (sr 1 230399 345599 (by norm_num) (by norm_num) (sr 1 345599 518399 (by norm_num) (by norm_num) (sr 1 518399 777599 (by norm_num) (by norm_num) (sr 1 777599 1166399 (by norm_num) (by norm_num) (sr 1 1166399 1749599 (by norm_num) (by norm_num) (sr 1 1749599 2624399 (by norm_num) (by norm_num) (sr 1 2624399 3936599 (by norm_num) (by norm_num) (sr 1 3936599 5904899 (by norm_num) (by norm_num) (sr 1 5904899 8857349 (by norm_num) (by norm_num) (sr 4 8857349 1660753 (by norm_num) (by norm_num) (sr 2 1660753 1245565 (by norm_num) (by norm_num) (sr 3 1245565 467087 (by norm_num) (by norm_num) (sr 1 467087 700631 (by norm_num) (by norm_num) (sr 1 700631 1050947 (by norm_num) (by norm_num) (sr 1 1050947 1576421 (by norm_num) (by norm_num) (sr 4 1576421 295579 (by norm_num) (by norm_num) (sr 1 295579 443369 (by norm_num) (by norm_num) (sr 2 443369 332527 (by norm_num) (by norm_num) (sr 1 332527 498791 (by norm_num) (by norm_num) (sr 1 498791 748187 (by norm_num) (by norm_num) (sr 1 748187 1122281 (by norm_num) (by norm_num) (sr 2 1122281 841711 (by norm_num) (by norm_num) (sr 1 841711 1262567 (by norm_num) (by norm_num) (sr 1 1262567 1893851 (by norm_num) (by norm_num) (sr 1 1893851 2840777 (by norm_num) (by norm_num) (sr 2 2840777 2130583 (by norm_num) (by norm_num) (sr 1 2130583 3195875 (by norm_num) (by norm_num) (sr 1 3195875 4793813 (by norm_num) (by norm_num) (sr 7 4793813 112355 (by norm_num) (by norm_num) (sr 1 112355 168533 (by norm_num) (by norm_num) (sr 8 168533 1975 (by norm_num) (by norm_num) (B 1975 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))))))
theorem R102403 : Reach 102403 := (sr 1 102403 153605 (by norm_num) (by norm_num) (sr 4 153605 28801 (by norm_num) (by norm_num) (B 28801 (by norm_num) (by norm_num) (by norm_num))))
theorem R102407 : Reach 102407 := (sr 1 102407 153611 (by norm_num) (by norm_num) (sr 1 153611 230417 (by norm_num) (by norm_num) (sr 2 230417 172813 (by norm_num) (by norm_num) (sr 3 172813 64805 (by norm_num) (by norm_num) (B 64805 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102411 : Reach 102411 := (sr 1 102411 153617 (by norm_num) (by norm_num) (sr 2 153617 115213 (by norm_num) (by norm_num) (sr 3 115213 43205 (by norm_num) (by norm_num) (B 43205 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102415 : Reach 102415 := (sr 1 102415 153623 (by norm_num) (by norm_num) (sr 1 153623 230435 (by norm_num) (by norm_num) (sr 1 230435 345653 (by norm_num) (by norm_num) (sr 5 345653 32405 (by norm_num) (by norm_num) (B 32405 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102419 : Reach 102419 := (sr 1 102419 153629 (by norm_num) (by norm_num) (sr 3 153629 57611 (by norm_num) (by norm_num) (B 57611 (by norm_num) (by norm_num) (by norm_num))))
theorem R102423 : Reach 102423 := (sr 1 102423 153635 (by norm_num) (by norm_num) (sr 1 153635 230453 (by norm_num) (by norm_num) (sr 5 230453 21605 (by norm_num) (by norm_num) (B 21605 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102427 : Reach 102427 := (sr 1 102427 153641 (by norm_num) (by norm_num) (sr 2 153641 115231 (by norm_num) (by norm_num) (sr 1 115231 172847 (by norm_num) (by norm_num) (sr 1 172847 259271 (by norm_num) (by norm_num) (sr 1 259271 388907 (by norm_num) (by norm_num) (sr 1 388907 583361 (by norm_num) (by norm_num) (sr 2 583361 437521 (by norm_num) (by norm_num) (sr 2 437521 328141 (by norm_num) (by norm_num) (sr 3 328141 123053 (by norm_num) (by norm_num) (sr 3 123053 46145 (by norm_num) (by norm_num) (B 46145 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R102431 : Reach 102431 := (sr 1 102431 153647 (by norm_num) (by norm_num) (sr 1 153647 230471 (by norm_num) (by norm_num) (sr 1 230471 345707 (by norm_num) (by norm_num) (sr 1 345707 518561 (by norm_num) (by norm_num) (sr 2 518561 388921 (by norm_num) (by norm_num) (sr 2 388921 291691 (by norm_num) (by norm_num) (sr 1 291691 437537 (by norm_num) (by norm_num) (sr 2 437537 328153 (by norm_num) (by norm_num) (sr 2 328153 246115 (by norm_num) (by norm_num) (sr 1 246115 369173 (by norm_num) (by norm_num) (sr 6 369173 17305 (by norm_num) (by norm_num) (B 17305 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R102435 : Reach 102435 := (sr 1 102435 153653 (by norm_num) (by norm_num) (sr 5 153653 14405 (by norm_num) (by norm_num) (B 14405 (by norm_num) (by norm_num) (by norm_num))))
theorem R102439 : Reach 102439 := (sr 1 102439 153659 (by norm_num) (by norm_num) (sr 1 153659 230489 (by norm_num) (by norm_num) (sr 2 230489 172867 (by norm_num) (by norm_num) (sr 1 172867 259301 (by norm_num) (by norm_num) (sr 4 259301 48619 (by norm_num) (by norm_num) (B 48619 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102443 : Reach 102443 := (sr 1 102443 153665 (by norm_num) (by norm_num) (sr 2 153665 115249 (by norm_num) (by norm_num) (sr 2 115249 86437 (by norm_num) (by norm_num) (B 86437 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102447 : Reach 102447 := (sr 1 102447 153671 (by norm_num) (by norm_num) (sr 1 153671 230507 (by norm_num) (by norm_num) (sr 1 230507 345761 (by norm_num) (by norm_num) (sr 2 345761 259321 (by norm_num) (by norm_num) (sr 2 259321 194491 (by norm_num) (by norm_num) (sr 1 194491 291737 (by norm_num) (by norm_num) (sr 2 291737 218803 (by norm_num) (by norm_num) (sr 1 218803 328205 (by norm_num) (by norm_num) (sr 3 328205 123077 (by norm_num) (by norm_num) (sr 4 123077 23077 (by norm_num) (by norm_num) (B 23077 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R102451 : Reach 102451 := (sr 1 102451 153677 (by norm_num) (by norm_num) (sr 3 153677 57629 (by norm_num) (by norm_num) (B 57629 (by norm_num) (by norm_num) (by norm_num))))
theorem R102455 : Reach 102455 := (sr 1 102455 153683 (by norm_num) (by norm_num) (sr 1 153683 230525 (by norm_num) (by norm_num) (sr 3 230525 86447 (by norm_num) (by norm_num) (B 86447 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102459 : Reach 102459 := (sr 1 102459 153689 (by norm_num) (by norm_num) (sr 2 153689 115267 (by norm_num) (by norm_num) (sr 1 115267 172901 (by norm_num) (by norm_num) (sr 4 172901 32419 (by norm_num) (by norm_num) (B 32419 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102463 : Reach 102463 := (sr 1 102463 153695 (by norm_num) (by norm_num) (sr 1 153695 230543 (by norm_num) (by norm_num) (sr 1 230543 345815 (by norm_num) (by norm_num) (sr 1 345815 518723 (by norm_num) (by norm_num) (sr 1 518723 778085 (by norm_num) (by norm_num) (sr 4 778085 145891 (by norm_num) (by norm_num) (sr 1 145891 218837 (by norm_num) (by norm_num) (sr 7 218837 5129 (by norm_num) (by norm_num) (B 5129 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R102467 : Reach 102467 := (sr 1 102467 153701 (by norm_num) (by norm_num) (sr 4 153701 28819 (by norm_num) (by norm_num) (B 28819 (by norm_num) (by norm_num) (by norm_num))))
theorem R102471 : Reach 102471 := (sr 1 102471 153707 (by norm_num) (by norm_num) (sr 1 153707 230561 (by norm_num) (by norm_num) (sr 2 230561 172921 (by norm_num) (by norm_num) (sr 2 172921 129691 (by norm_num) (by norm_num) (sr 1 129691 194537 (by norm_num) (by norm_num) (sr 2 194537 145903 (by norm_num) (by norm_num) (sr 1 145903 218855 (by norm_num) (by norm_num) (sr 1 218855 328283 (by norm_num) (by norm_num) (sr 1 328283 492425 (by norm_num) (by norm_num) (sr 2 492425 369319 (by norm_num) (by norm_num) (sr 1 369319 553979 (by norm_num) (by norm_num) (sr 1 553979 830969 (by norm_num) (by norm_num) (sr 2 830969 623227 (by norm_num) (by norm_num) (sr 1 623227 934841 (by norm_num) (by norm_num) (sr 2 934841 701131 (by norm_num) (by norm_num) (sr 1 701131 1051697 (by norm_num) (by norm_num) (sr 2 1051697 788773 (by norm_num) (by norm_num) (sr 4 788773 147895 (by norm_num) (by norm_num) (sr 1 147895 221843 (by norm_num) (by norm_num) (sr 1 221843 332765 (by norm_num) (by norm_num) (sr 3 332765 124787 (by norm_num) (by norm_num) (sr 1 124787 187181 (by norm_num) (by norm_num) (sr 3 187181 70193 (by norm_num) (by norm_num) (B 70193 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))
theorem R102475 : Reach 102475 := (sr 1 102475 153713 (by norm_num) (by norm_num) (sr 2 153713 115285 (by norm_num) (by norm_num) (sr 8 115285 1351 (by norm_num) (by norm_num) (B 1351 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102479 : Reach 102479 := (sr 1 102479 153719 (by norm_num) (by norm_num) (sr 1 153719 230579 (by norm_num) (by norm_num) (sr 1 230579 345869 (by norm_num) (by norm_num) (sr 3 345869 129701 (by norm_num) (by norm_num) (sr 4 129701 24319 (by norm_num) (by norm_num) (B 24319 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102483 : Reach 102483 := (sr 1 102483 153725 (by norm_num) (by norm_num) (sr 3 153725 57647 (by norm_num) (by norm_num) (B 57647 (by norm_num) (by norm_num) (by norm_num))))
theorem R102487 : Reach 102487 := (sr 1 102487 153731 (by norm_num) (by norm_num) (sr 1 153731 230597 (by norm_num) (by norm_num) (sr 4 230597 43237 (by norm_num) (by norm_num) (B 43237 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102491 : Reach 102491 := (sr 1 102491 153737 (by norm_num) (by norm_num) (sr 2 153737 115303 (by norm_num) (by norm_num) (sr 1 115303 172955 (by norm_num) (by norm_num) (sr 1 172955 259433 (by norm_num) (by norm_num) (sr 2 259433 194575 (by norm_num) (by norm_num) (sr 1 194575 291863 (by norm_num) (by norm_num) (sr 1 291863 437795 (by norm_num) (by norm_num) (sr 1 437795 656693 (by norm_num) (by norm_num) (sr 5 656693 61565 (by norm_num) (by norm_num) (B 61565 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R102495 : Reach 102495 := (sr 1 102495 153743 (by norm_num) (by norm_num) (sr 1 153743 230615 (by norm_num) (by norm_num) (sr 1 230615 345923 (by norm_num) (by norm_num) (sr 1 345923 518885 (by norm_num) (by norm_num) (sr 4 518885 97291 (by norm_num) (by norm_num) (B 97291 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102499 : Reach 102499 := (sr 1 102499 153749 (by norm_num) (by norm_num) (sr 6 153749 7207 (by norm_num) (by norm_num) (B 7207 (by norm_num) (by norm_num) (by norm_num))))
theorem R102503 : Reach 102503 := (sr 1 102503 153755 (by norm_num) (by norm_num) (sr 1 153755 230633 (by norm_num) (by norm_num) (sr 2 230633 172975 (by norm_num) (by norm_num) (sr 1 172975 259463 (by norm_num) (by norm_num) (sr 1 259463 389195 (by norm_num) (by norm_num) (sr 1 389195 583793 (by norm_num) (by norm_num) (sr 2 583793 437845 (by norm_num) (by norm_num) (sr 8 437845 5131 (by norm_num) (by norm_num) (B 5131 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R102507 : Reach 102507 := (sr 1 102507 153761 (by norm_num) (by norm_num) (sr 2 153761 115321 (by norm_num) (by norm_num) (sr 2 115321 86491 (by norm_num) (by norm_num) (B 86491 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102511 : Reach 102511 := (sr 1 102511 153767 (by norm_num) (by norm_num) (sr 1 153767 230651 (by norm_num) (by norm_num) (sr 1 230651 345977 (by norm_num) (by norm_num) (sr 2 345977 259483 (by norm_num) (by norm_num) (sr 1 259483 389225 (by norm_num) (by norm_num) (sr 2 389225 291919 (by norm_num) (by norm_num) (sr 1 291919 437879 (by norm_num) (by norm_num) (sr 1 437879 656819 (by norm_num) (by norm_num) (sr 1 656819 985229 (by norm_num) (by norm_num) (sr 3 985229 369461 (by norm_num) (by norm_num) (sr 5 369461 34637 (by norm_num) (by norm_num) (B 34637 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R102515 : Reach 102515 := (sr 1 102515 153773 (by norm_num) (by norm_num) (sr 3 153773 57665 (by norm_num) (by norm_num) (B 57665 (by norm_num) (by norm_num) (by norm_num))))
theorem R102519 : Reach 102519 := (sr 1 102519 153779 (by norm_num) (by norm_num) (sr 1 153779 230669 (by norm_num) (by norm_num) (sr 3 230669 86501 (by norm_num) (by norm_num) (B 86501 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102523 : Reach 102523 := (sr 1 102523 153785 (by norm_num) (by norm_num) (sr 2 153785 115339 (by norm_num) (by norm_num) (sr 1 115339 173009 (by norm_num) (by norm_num) (sr 2 173009 129757 (by norm_num) (by norm_num) (sr 3 129757 48659 (by norm_num) (by norm_num) (B 48659 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102527 : Reach 102527 := (sr 1 102527 153791 (by norm_num) (by norm_num) (sr 1 153791 230687 (by norm_num) (by norm_num) (sr 1 230687 346031 (by norm_num) (by norm_num) (sr 1 346031 519047 (by norm_num) (by norm_num) (sr 1 519047 778571 (by norm_num) (by norm_num) (sr 1 778571 1167857 (by norm_num) (by norm_num) (sr 2 1167857 875893 (by norm_num) (by norm_num) (sr 5 875893 82115 (by norm_num) (by norm_num) (B 82115 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R102531 : Reach 102531 := (sr 1 102531 153797 (by norm_num) (by norm_num) (sr 4 153797 28837 (by norm_num) (by norm_num) (B 28837 (by norm_num) (by norm_num) (by norm_num))))
theorem R102535 : Reach 102535 := (sr 1 102535 153803 (by norm_num) (by norm_num) (sr 1 153803 230705 (by norm_num) (by norm_num) (sr 2 230705 173029 (by norm_num) (by norm_num) (sr 4 173029 32443 (by norm_num) (by norm_num) (B 32443 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102539 : Reach 102539 := (sr 1 102539 153809 (by norm_num) (by norm_num) (sr 2 153809 115357 (by norm_num) (by norm_num) (sr 3 115357 43259 (by norm_num) (by norm_num) (B 43259 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102543 : Reach 102543 := (sr 1 102543 153815 (by norm_num) (by norm_num) (sr 1 153815 230723 (by norm_num) (by norm_num) (sr 1 230723 346085 (by norm_num) (by norm_num) (sr 4 346085 64891 (by norm_num) (by norm_num) (B 64891 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102547 : Reach 102547 := (sr 1 102547 153821 (by norm_num) (by norm_num) (sr 3 153821 57683 (by norm_num) (by norm_num) (B 57683 (by norm_num) (by norm_num) (by norm_num))))
theorem R102551 : Reach 102551 := (sr 1 102551 153827 (by norm_num) (by norm_num) (sr 1 153827 230741 (by norm_num) (by norm_num) (sr 12 230741 169 (by norm_num) (by norm_num) (B 169 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102555 : Reach 102555 := (sr 1 102555 153833 (by norm_num) (by norm_num) (sr 2 153833 115375 (by norm_num) (by norm_num) (sr 1 115375 173063 (by norm_num) (by norm_num) (sr 1 173063 259595 (by norm_num) (by norm_num) (sr 1 259595 389393 (by norm_num) (by norm_num) (sr 2 389393 292045 (by norm_num) (by norm_num) (sr 3 292045 109517 (by norm_num) (by norm_num) (sr 3 109517 41069 (by norm_num) (by norm_num) (B 41069 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R102559 : Reach 102559 := (sr 1 102559 153839 (by norm_num) (by norm_num) (sr 1 153839 230759 (by norm_num) (by norm_num) (sr 1 230759 346139 (by norm_num) (by norm_num) (sr 1 346139 519209 (by norm_num) (by norm_num) (sr 2 519209 389407 (by norm_num) (by norm_num) (sr 1 389407 584111 (by norm_num) (by norm_num) (sr 1 584111 876167 (by norm_num) (by norm_num) (sr 1 876167 1314251 (by norm_num) (by norm_num) (sr 1 1314251 1971377 (by norm_num) (by norm_num) (sr 2 1971377 1478533 (by norm_num) (by norm_num) (sr 4 1478533 277225 (by norm_num) (by norm_num) (sr 2 277225 207919 (by norm_num) (by norm_num) (sr 1 207919 311879 (by norm_num) (by norm_num) (sr 1 311879 467819 (by norm_num) (by norm_num) (sr 1 467819 701729 (by norm_num) (by norm_num) (sr 2 701729 526297 (by norm_num) (by norm_num) (sr 2 526297 394723 (by norm_num) (by norm_num) (sr 1 394723 592085 (by norm_num) (by norm_num) (sr 7 592085 13877 (by norm_num) (by norm_num) (B 13877 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))
theorem R102563 : Reach 102563 := (sr 1 102563 153845 (by norm_num) (by norm_num) (sr 5 153845 14423 (by norm_num) (by norm_num) (B 14423 (by norm_num) (by norm_num) (by norm_num))))
theorem R102567 : Reach 102567 := (sr 1 102567 153851 (by norm_num) (by norm_num) (sr 1 153851 230777 (by norm_num) (by norm_num) (sr 2 230777 173083 (by norm_num) (by norm_num) (sr 1 173083 259625 (by norm_num) (by norm_num) (sr 2 259625 194719 (by norm_num) (by norm_num) (sr 1 194719 292079 (by norm_num) (by norm_num) (sr 1 292079 438119 (by norm_num) (by norm_num) (sr 1 438119 657179 (by norm_num) (by norm_num) (sr 1 657179 985769 (by norm_num) (by norm_num) (sr 2 985769 739327 (by norm_num) (by norm_num) (sr 1 739327 1108991 (by norm_num) (by norm_num) (sr 1 1108991 1663487 (by norm_num) (by norm_num) (sr 1 1663487 2495231 (by norm_num) (by norm_num) (sr 1 2495231 3742847 (by norm_num) (by norm_num) (sr 1 3742847 5614271 (by norm_num) (by norm_num) (sr 1 5614271 8421407 (by norm_num) (by norm_num) (sr 1 8421407 12632111 (by norm_num) (by norm_num) (sr 1 12632111 18948167 (by norm_num) (by norm_num) (sr 1 18948167 28422251 (by norm_num) (by norm_num) (sr 1 28422251 42633377 (by norm_num) (by norm_num) (sr 2 42633377 31975033 (by norm_num) (by norm_num) (sr 2 31975033 23981275 (by norm_num) (by norm_num) (sr 1 23981275 35971913 (by norm_num) (by norm_num) (sr 2 35971913 26978935 (by norm_num) (by norm_num) (sr 1 26978935 40468403 (by norm_num) (by norm_num) (sr 1 40468403 60702605 (by norm_num) (by norm_num) (sr 3 60702605 22763477 (by norm_num) (by norm_num) (sr 7 22763477 533519 (by norm_num) (by norm_num) (sr 1 533519 800279 (by norm_num) (by norm_num) (sr 1 800279 1200419 (by norm_num) (by norm_num) (sr 1 1200419 1800629 (by norm_num) (by norm_num) (sr 5 1800629 168809 (by norm_num) (by norm_num) (sr 2 168809 126607 (by norm_num) (by norm_num) (sr 1 126607 189911 (by norm_num) (by norm_num) (sr 1 189911 284867 (by norm_num) (by norm_num) (sr 1 284867 427301 (by norm_num) (by norm_num) (sr 4 427301 80119 (by norm_num) (by norm_num) (B 80119 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))))))))))
theorem R102571 : Reach 102571 := (sr 1 102571 153857 (by norm_num) (by norm_num) (sr 2 153857 115393 (by norm_num) (by norm_num) (sr 2 115393 86545 (by norm_num) (by norm_num) (B 86545 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102575 : Reach 102575 := (sr 1 102575 153863 (by norm_num) (by norm_num) (sr 1 153863 230795 (by norm_num) (by norm_num) (sr 1 230795 346193 (by norm_num) (by norm_num) (sr 2 346193 259645 (by norm_num) (by norm_num) (sr 3 259645 97367 (by norm_num) (by norm_num) (B 97367 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102579 : Reach 102579 := (sr 1 102579 153869 (by norm_num) (by norm_num) (sr 3 153869 57701 (by norm_num) (by norm_num) (B 57701 (by norm_num) (by norm_num) (by norm_num))))
theorem R102583 : Reach 102583 := (sr 1 102583 153875 (by norm_num) (by norm_num) (sr 1 153875 230813 (by norm_num) (by norm_num) (sr 3 230813 86555 (by norm_num) (by norm_num) (B 86555 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102587 : Reach 102587 := (sr 1 102587 153881 (by norm_num) (by norm_num) (sr 2 153881 115411 (by norm_num) (by norm_num) (sr 1 115411 173117 (by norm_num) (by norm_num) (sr 3 173117 64919 (by norm_num) (by norm_num) (B 64919 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102591 : Reach 102591 := (sr 1 102591 153887 (by norm_num) (by norm_num) (sr 1 153887 230831 (by norm_num) (by norm_num) (sr 1 230831 346247 (by norm_num) (by norm_num) (sr 1 346247 519371 (by norm_num) (by norm_num) (sr 1 519371 779057 (by norm_num) (by norm_num) (sr 2 779057 584293 (by norm_num) (by norm_num) (sr 4 584293 109555 (by norm_num) (by norm_num) (sr 1 109555 164333 (by norm_num) (by norm_num) (sr 3 164333 61625 (by norm_num) (by norm_num) (B 61625 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R102595 : Reach 102595 := (sr 1 102595 153893 (by norm_num) (by norm_num) (sr 4 153893 28855 (by norm_num) (by norm_num) (B 28855 (by norm_num) (by norm_num) (by norm_num))))
theorem R102599 : Reach 102599 := (sr 1 102599 153899 (by norm_num) (by norm_num) (sr 1 153899 230849 (by norm_num) (by norm_num) (sr 2 230849 173137 (by norm_num) (by norm_num) (sr 2 173137 129853 (by norm_num) (by norm_num) (sr 3 129853 48695 (by norm_num) (by norm_num) (B 48695 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102603 : Reach 102603 := (sr 1 102603 153905 (by norm_num) (by norm_num) (sr 2 153905 115429 (by norm_num) (by norm_num) (sr 4 115429 21643 (by norm_num) (by norm_num) (B 21643 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102607 : Reach 102607 := (sr 1 102607 153911 (by norm_num) (by norm_num) (sr 1 153911 230867 (by norm_num) (by norm_num) (sr 1 230867 346301 (by norm_num) (by norm_num) (sr 3 346301 129863 (by norm_num) (by norm_num) (sr 1 129863 194795 (by norm_num) (by norm_num) (sr 1 194795 292193 (by norm_num) (by norm_num) (sr 2 292193 219145 (by norm_num) (by norm_num) (sr 2 219145 164359 (by norm_num) (by norm_num) (sr 1 164359 246539 (by norm_num) (by norm_num) (sr 1 246539 369809 (by norm_num) (by norm_num) (sr 2 369809 277357 (by norm_num) (by norm_num) (sr 3 277357 104009 (by norm_num) (by norm_num) (sr 2 104009 78007 (by norm_num) (by norm_num) (B 78007 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R102611 : Reach 102611 := (sr 1 102611 153917 (by norm_num) (by norm_num) (sr 3 153917 57719 (by norm_num) (by norm_num) (B 57719 (by norm_num) (by norm_num) (by norm_num))))
theorem R102615 : Reach 102615 := (sr 1 102615 153923 (by norm_num) (by norm_num) (sr 1 153923 230885 (by norm_num) (by norm_num) (sr 4 230885 43291 (by norm_num) (by norm_num) (B 43291 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102619 : Reach 102619 := (sr 1 102619 153929 (by norm_num) (by norm_num) (sr 2 153929 115447 (by norm_num) (by norm_num) (sr 1 115447 173171 (by norm_num) (by norm_num) (sr 1 173171 259757 (by norm_num) (by norm_num) (sr 3 259757 97409 (by norm_num) (by norm_num) (B 97409 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102623 : Reach 102623 := (sr 1 102623 153935 (by norm_num) (by norm_num) (sr 1 153935 230903 (by norm_num) (by norm_num) (sr 1 230903 346355 (by norm_num) (by norm_num) (sr 1 346355 519533 (by norm_num) (by norm_num) (sr 3 519533 194825 (by norm_num) (by norm_num) (sr 2 194825 146119 (by norm_num) (by norm_num) (sr 1 146119 219179 (by norm_num) (by norm_num) (sr 1 219179 328769 (by norm_num) (by norm_num) (sr 2 328769 246577 (by norm_num) (by norm_num) (sr 2 246577 184933 (by norm_num) (by norm_num) (sr 4 184933 34675 (by norm_num) (by norm_num) (B 34675 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R102627 : Reach 102627 := (sr 1 102627 153941 (by norm_num) (by norm_num) (sr 10 153941 451 (by norm_num) (by norm_num) (B 451 (by norm_num) (by norm_num) (by norm_num))))
theorem R102631 : Reach 102631 := (sr 1 102631 153947 (by norm_num) (by norm_num) (sr 1 153947 230921 (by norm_num) (by norm_num) (sr 2 230921 173191 (by norm_num) (by norm_num) (sr 1 173191 259787 (by norm_num) (by norm_num) (sr 1 259787 389681 (by norm_num) (by norm_num) (sr 2 389681 292261 (by norm_num) (by norm_num) (sr 4 292261 54799 (by norm_num) (by norm_num) (B 54799 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R102635 : Reach 102635 := (sr 1 102635 153953 (by norm_num) (by norm_num) (sr 2 153953 115465 (by norm_num) (by norm_num) (sr 2 115465 86599 (by norm_num) (by norm_num) (B 86599 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102639 : Reach 102639 := (sr 1 102639 153959 (by norm_num) (by norm_num) (sr 1 153959 230939 (by norm_num) (by norm_num) (sr 1 230939 346409 (by norm_num) (by norm_num) (sr 2 346409 259807 (by norm_num) (by norm_num) (sr 1 259807 389711 (by norm_num) (by norm_num) (sr 1 389711 584567 (by norm_num) (by norm_num) (sr 1 584567 876851 (by norm_num) (by norm_num) (sr 1 876851 1315277 (by norm_num) (by norm_num) (sr 3 1315277 493229 (by norm_num) (by norm_num) (sr 3 493229 184961 (by norm_num) (by norm_num) (sr 2 184961 138721 (by norm_num) (by norm_num) (sr 2 138721 104041 (by norm_num) (by norm_num) (sr 2 104041 78031 (by norm_num) (by norm_num) (B 78031 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R102643 : Reach 102643 := (sr 1 102643 153965 (by norm_num) (by norm_num) (sr 3 153965 57737 (by norm_num) (by norm_num) (B 57737 (by norm_num) (by norm_num) (by norm_num))))
theorem R102647 : Reach 102647 := (sr 1 102647 153971 (by norm_num) (by norm_num) (sr 1 153971 230957 (by norm_num) (by norm_num) (sr 3 230957 86609 (by norm_num) (by norm_num) (B 86609 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102651 : Reach 102651 := (sr 1 102651 153977 (by norm_num) (by norm_num) (sr 2 153977 115483 (by norm_num) (by norm_num) (sr 1 115483 173225 (by norm_num) (by norm_num) (sr 2 173225 129919 (by norm_num) (by norm_num) (sr 1 129919 194879 (by norm_num) (by norm_num) (sr 1 194879 292319 (by norm_num) (by norm_num) (sr 1 292319 438479 (by norm_num) (by norm_num) (sr 1 438479 657719 (by norm_num) (by norm_num) (sr 1 657719 986579 (by norm_num) (by norm_num) (sr 1 986579 1479869 (by norm_num) (by norm_num) (sr 3 1479869 554951 (by norm_num) (by norm_num) (sr 1 554951 832427 (by norm_num) (by norm_num) (sr 1 832427 1248641 (by norm_num) (by norm_num) (sr 2 1248641 936481 (by norm_num) (by norm_num) (sr 2 936481 702361 (by norm_num) (by norm_num) (sr 2 702361 526771 (by norm_num) (by norm_num) (sr 1 526771 790157 (by norm_num) (by norm_num) (sr 3 790157 296309 (by norm_num) (by norm_num) (sr 5 296309 27779 (by norm_num) (by norm_num) (B 27779 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))
theorem R102655 : Reach 102655 := (sr 1 102655 153983 (by norm_num) (by norm_num) (sr 1 153983 230975 (by norm_num) (by norm_num) (sr 1 230975 346463 (by norm_num) (by norm_num) (sr 1 346463 519695 (by norm_num) (by norm_num) (sr 1 519695 779543 (by norm_num) (by norm_num) (sr 1 779543 1169315 (by norm_num) (by norm_num) (sr 1 1169315 1753973 (by norm_num) (by norm_num) (sr 5 1753973 164435 (by norm_num) (by norm_num) (sr 1 164435 246653 (by norm_num) (by norm_num) (sr 3 246653 92495 (by norm_num) (by norm_num) (B 92495 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R102659 : Reach 102659 := (sr 1 102659 153989 (by norm_num) (by norm_num) (sr 4 153989 28873 (by norm_num) (by norm_num) (B 28873 (by norm_num) (by norm_num) (by norm_num))))
theorem R102663 : Reach 102663 := (sr 1 102663 153995 (by norm_num) (by norm_num) (sr 1 153995 230993 (by norm_num) (by norm_num) (sr 2 230993 173245 (by norm_num) (by norm_num) (sr 3 173245 64967 (by norm_num) (by norm_num) (B 64967 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102667 : Reach 102667 := (sr 1 102667 154001 (by norm_num) (by norm_num) (sr 2 154001 115501 (by norm_num) (by norm_num) (sr 3 115501 43313 (by norm_num) (by norm_num) (B 43313 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102671 : Reach 102671 := (sr 1 102671 154007 (by norm_num) (by norm_num) (sr 1 154007 231011 (by norm_num) (by norm_num) (sr 1 231011 346517 (by norm_num) (by norm_num) (sr 6 346517 16243 (by norm_num) (by norm_num) (B 16243 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102675 : Reach 102675 := (sr 1 102675 154013 (by norm_num) (by norm_num) (sr 3 154013 57755 (by norm_num) (by norm_num) (B 57755 (by norm_num) (by norm_num) (by norm_num))))
theorem R102679 : Reach 102679 := (sr 1 102679 154019 (by norm_num) (by norm_num) (sr 1 154019 231029 (by norm_num) (by norm_num) (sr 5 231029 21659 (by norm_num) (by norm_num) (B 21659 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102683 : Reach 102683 := (sr 1 102683 154025 (by norm_num) (by norm_num) (sr 2 154025 115519 (by norm_num) (by norm_num) (sr 1 115519 173279 (by norm_num) (by norm_num) (sr 1 173279 259919 (by norm_num) (by norm_num) (sr 1 259919 389879 (by norm_num) (by norm_num) (sr 1 389879 584819 (by norm_num) (by norm_num) (sr 1 584819 877229 (by norm_num) (by norm_num) (sr 3 877229 328961 (by norm_num) (by norm_num) (sr 2 328961 246721 (by norm_num) (by norm_num) (sr 2 246721 185041 (by norm_num) (by norm_num) (sr 2 185041 138781 (by norm_num) (by norm_num) (sr 3 138781 52043 (by norm_num) (by norm_num) (B 52043 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R102687 : Reach 102687 := (sr 1 102687 154031 (by norm_num) (by norm_num) (sr 1 154031 231047 (by norm_num) (by norm_num) (sr 1 231047 346571 (by norm_num) (by norm_num) (sr 1 346571 519857 (by norm_num) (by norm_num) (sr 2 519857 389893 (by norm_num) (by norm_num) (sr 4 389893 73105 (by norm_num) (by norm_num) (B 73105 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R102691 : Reach 102691 := (sr 1 102691 154037 (by norm_num) (by norm_num) (sr 5 154037 14441 (by norm_num) (by norm_num) (B 14441 (by norm_num) (by norm_num) (by norm_num))))
theorem R102695 : Reach 102695 := (sr 1 102695 154043 (by norm_num) (by norm_num) (sr 1 154043 231065 (by norm_num) (by norm_num) (sr 2 231065 173299 (by norm_num) (by norm_num) (sr 1 173299 259949 (by norm_num) (by norm_num) (sr 3 259949 97481 (by norm_num) (by norm_num) (B 97481 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102699 : Reach 102699 := (sr 1 102699 154049 (by norm_num) (by norm_num) (sr 2 154049 115537 (by norm_num) (by norm_num) (sr 2 115537 86653 (by norm_num) (by norm_num) (B 86653 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102703 : Reach 102703 := (sr 1 102703 154055 (by norm_num) (by norm_num) (sr 1 154055 231083 (by norm_num) (by norm_num) (sr 1 231083 346625 (by norm_num) (by norm_num) (sr 2 346625 259969 (by norm_num) (by norm_num) (sr 2 259969 194977 (by norm_num) (by norm_num) (sr 2 194977 146233 (by norm_num) (by norm_num) (sr 2 146233 109675 (by norm_num) (by norm_num) (sr 1 109675 164513 (by norm_num) (by norm_num) (sr 2 164513 123385 (by norm_num) (by norm_num) (sr 2 123385 92539 (by norm_num) (by norm_num) (B 92539 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R102707 : Reach 102707 := (sr 1 102707 154061 (by norm_num) (by norm_num) (sr 3 154061 57773 (by norm_num) (by norm_num) (B 57773 (by norm_num) (by norm_num) (by norm_num))))
theorem R102711 : Reach 102711 := (sr 1 102711 154067 (by norm_num) (by norm_num) (sr 1 154067 231101 (by norm_num) (by norm_num) (sr 3 231101 86663 (by norm_num) (by norm_num) (B 86663 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102715 : Reach 102715 := (sr 1 102715 154073 (by norm_num) (by norm_num) (sr 2 154073 115555 (by norm_num) (by norm_num) (sr 1 115555 173333 (by norm_num) (by norm_num) (sr 6 173333 8125 (by norm_num) (by norm_num) (B 8125 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102719 : Reach 102719 := (sr 1 102719 154079 (by norm_num) (by norm_num) (sr 1 154079 231119 (by norm_num) (by norm_num) (sr 1 231119 346679 (by norm_num) (by norm_num) (sr 1 346679 520019 (by norm_num) (by norm_num) (sr 1 520019 780029 (by norm_num) (by norm_num) (sr 3 780029 292511 (by norm_num) (by norm_num) (sr 1 292511 438767 (by norm_num) (by norm_num) (sr 1 438767 658151 (by norm_num) (by norm_num) (sr 1 658151 987227 (by norm_num) (by norm_num) (sr 1 987227 1480841 (by norm_num) (by norm_num) (sr 2 1480841 1110631 (by norm_num) (by norm_num) (sr 1 1110631 1665947 (by norm_num) (by norm_num) (sr 1 1665947 2498921 (by norm_num) (by norm_num) (sr 2 2498921 1874191 (by norm_num) (by norm_num) (sr 1 1874191 2811287 (by norm_num) (by norm_num) (sr 1 2811287 4216931 (by norm_num) (by norm_num) (sr 1 4216931 6325397 (by norm_num) (by norm_num) (sr 6 6325397 296503 (by norm_num) (by norm_num) (sr 1 296503 444755 (by norm_num) (by norm_num) (sr 1 444755 667133 (by norm_num) (by norm_num) (sr 3 667133 250175 (by norm_num) (by norm_num) (sr 1 250175 375263 (by norm_num) (by norm_num) (sr 1 375263 562895 (by norm_num) (by norm_num) (sr 1 562895 844343 (by norm_num) (by norm_num) (sr 1 844343 1266515 (by norm_num) (by norm_num) (sr 1 1266515 1899773 (by norm_num) (by norm_num) (sr 3 1899773 712415 (by norm_num) (by norm_num) (sr 1 712415 1068623 (by norm_num) (by norm_num) (sr 1 1068623 1602935 (by norm_num) (by norm_num) (sr 1 1602935 2404403 (by norm_num) (by norm_num) (sr 1 2404403 3606605 (by norm_num) (by norm_num) (sr 3 3606605 1352477 (by norm_num) (by norm_num) (sr 3 1352477 507179 (by norm_num) (by norm_num) (sr 1 507179 760769 (by norm_num) (by norm_num) (sr 2 760769 570577 (by norm_num) (by norm_num) (sr 2 570577 427933 (by norm_num) (by norm_num) (sr 3 427933 160475 (by norm_num) (by norm_num) (sr 1 160475 240713 (by norm_num) (by norm_num) (sr 2 240713 180535 (by norm_num) (by norm_num) (sr 1 180535 270803 (by norm_num) (by norm_num) (sr 1 270803 406205 (by norm_num) (by norm_num) (sr 3 406205 152327 (by norm_num) (by norm_num) (sr 1 152327 228491 (by norm_num) (by norm_num) (sr 1 228491 342737 (by norm_num) (by norm_num) (sr 2 342737 257053 (by norm_num) (by norm_num) (sr 3 257053 96395 (by norm_num) (by norm_num) (B 96395 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))))))))))))))))))))
theorem R102723 : Reach 102723 := (sr 1 102723 154085 (by norm_num) (by norm_num) (sr 4 154085 28891 (by norm_num) (by norm_num) (B 28891 (by norm_num) (by norm_num) (by norm_num))))
theorem R102727 : Reach 102727 := (sr 1 102727 154091 (by norm_num) (by norm_num) (sr 1 154091 231137 (by norm_num) (by norm_num) (sr 2 231137 173353 (by norm_num) (by norm_num) (sr 2 173353 130015 (by norm_num) (by norm_num) (sr 1 130015 195023 (by norm_num) (by norm_num) (sr 1 195023 292535 (by norm_num) (by norm_num) (sr 1 292535 438803 (by norm_num) (by norm_num) (sr 1 438803 658205 (by norm_num) (by norm_num) (sr 3 658205 246827 (by norm_num) (by norm_num) (sr 1 246827 370241 (by norm_num) (by norm_num) (sr 2 370241 277681 (by norm_num) (by norm_num) (sr 2 277681 208261 (by norm_num) (by norm_num) (sr 4 208261 39049 (by norm_num) (by norm_num) (B 39049 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R102731 : Reach 102731 := (sr 1 102731 154097 (by norm_num) (by norm_num) (sr 2 154097 115573 (by norm_num) (by norm_num) (sr 5 115573 10835 (by norm_num) (by norm_num) (B 10835 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102735 : Reach 102735 := (sr 1 102735 154103 (by norm_num) (by norm_num) (sr 1 154103 231155 (by norm_num) (by norm_num) (sr 1 231155 346733 (by norm_num) (by norm_num) (sr 3 346733 130025 (by norm_num) (by norm_num) (sr 2 130025 97519 (by norm_num) (by norm_num) (B 97519 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102739 : Reach 102739 := (sr 1 102739 154109 (by norm_num) (by norm_num) (sr 3 154109 57791 (by norm_num) (by norm_num) (B 57791 (by norm_num) (by norm_num) (by norm_num))))
theorem R102743 : Reach 102743 := (sr 1 102743 154115 (by norm_num) (by norm_num) (sr 1 154115 231173 (by norm_num) (by norm_num) (sr 4 231173 43345 (by norm_num) (by norm_num) (B 43345 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102747 : Reach 102747 := (sr 1 102747 154121 (by norm_num) (by norm_num) (sr 2 154121 115591 (by norm_num) (by norm_num) (sr 1 115591 173387 (by norm_num) (by norm_num) (sr 1 173387 260081 (by norm_num) (by norm_num) (sr 2 260081 195061 (by norm_num) (by norm_num) (sr 5 195061 18287 (by norm_num) (by norm_num) (B 18287 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R102751 : Reach 102751 := (sr 1 102751 154127 (by norm_num) (by norm_num) (sr 1 154127 231191 (by norm_num) (by norm_num) (sr 1 231191 346787 (by norm_num) (by norm_num) (sr 1 346787 520181 (by norm_num) (by norm_num) (sr 5 520181 48767 (by norm_num) (by norm_num) (B 48767 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102755 : Reach 102755 := (sr 1 102755 154133 (by norm_num) (by norm_num) (sr 6 154133 7225 (by norm_num) (by norm_num) (B 7225 (by norm_num) (by norm_num) (by norm_num))))
theorem R102759 : Reach 102759 := (sr 1 102759 154139 (by norm_num) (by norm_num) (sr 1 154139 231209 (by norm_num) (by norm_num) (sr 2 231209 173407 (by norm_num) (by norm_num) (sr 1 173407 260111 (by norm_num) (by norm_num) (sr 1 260111 390167 (by norm_num) (by norm_num) (sr 1 390167 585251 (by norm_num) (by norm_num) (sr 1 585251 877877 (by norm_num) (by norm_num) (sr 5 877877 82301 (by norm_num) (by norm_num) (B 82301 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R102763 : Reach 102763 := (sr 1 102763 154145 (by norm_num) (by norm_num) (sr 2 154145 115609 (by norm_num) (by norm_num) (sr 2 115609 86707 (by norm_num) (by norm_num) (B 86707 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102767 : Reach 102767 := (sr 1 102767 154151 (by norm_num) (by norm_num) (sr 1 154151 231227 (by norm_num) (by norm_num) (sr 1 231227 346841 (by norm_num) (by norm_num) (sr 2 346841 260131 (by norm_num) (by norm_num) (sr 1 260131 390197 (by norm_num) (by norm_num) (sr 5 390197 36581 (by norm_num) (by norm_num) (B 36581 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R102771 : Reach 102771 := (sr 1 102771 154157 (by norm_num) (by norm_num) (sr 3 154157 57809 (by norm_num) (by norm_num) (B 57809 (by norm_num) (by norm_num) (by norm_num))))
theorem R102775 : Reach 102775 := (sr 1 102775 154163 (by norm_num) (by norm_num) (sr 1 154163 231245 (by norm_num) (by norm_num) (sr 3 231245 86717 (by norm_num) (by norm_num) (B 86717 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102779 : Reach 102779 := (sr 1 102779 154169 (by norm_num) (by norm_num) (sr 2 154169 115627 (by norm_num) (by norm_num) (sr 1 115627 173441 (by norm_num) (by norm_num) (sr 2 173441 130081 (by norm_num) (by norm_num) (sr 2 130081 97561 (by norm_num) (by norm_num) (B 97561 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102783 : Reach 102783 := (sr 1 102783 154175 (by norm_num) (by norm_num) (sr 1 154175 231263 (by norm_num) (by norm_num) (sr 1 231263 346895 (by norm_num) (by norm_num) (sr 1 346895 520343 (by norm_num) (by norm_num) (sr 1 520343 780515 (by norm_num) (by norm_num) (sr 1 780515 1170773 (by norm_num) (by norm_num) (sr 11 1170773 1715 (by norm_num) (by norm_num) (B 1715 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R102787 : Reach 102787 := (sr 1 102787 154181 (by norm_num) (by norm_num) (sr 4 154181 28909 (by norm_num) (by norm_num) (B 28909 (by norm_num) (by norm_num) (by norm_num))))
theorem R102791 : Reach 102791 := (sr 1 102791 154187 (by norm_num) (by norm_num) (sr 1 154187 231281 (by norm_num) (by norm_num) (sr 2 231281 173461 (by norm_num) (by norm_num) (sr 6 173461 8131 (by norm_num) (by norm_num) (B 8131 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102795 : Reach 102795 := (sr 1 102795 154193 (by norm_num) (by norm_num) (sr 2 154193 115645 (by norm_num) (by norm_num) (sr 3 115645 43367 (by norm_num) (by norm_num) (B 43367 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102799 : Reach 102799 := (sr 1 102799 154199 (by norm_num) (by norm_num) (sr 1 154199 231299 (by norm_num) (by norm_num) (sr 1 231299 346949 (by norm_num) (by norm_num) (sr 4 346949 65053 (by norm_num) (by norm_num) (B 65053 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102803 : Reach 102803 := (sr 1 102803 154205 (by norm_num) (by norm_num) (sr 3 154205 57827 (by norm_num) (by norm_num) (B 57827 (by norm_num) (by norm_num) (by norm_num))))
theorem R102807 : Reach 102807 := (sr 1 102807 154211 (by norm_num) (by norm_num) (sr 1 154211 231317 (by norm_num) (by norm_num) (sr 6 231317 10843 (by norm_num) (by norm_num) (B 10843 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102811 : Reach 102811 := (sr 1 102811 154217 (by norm_num) (by norm_num) (sr 2 154217 115663 (by norm_num) (by norm_num) (sr 1 115663 173495 (by norm_num) (by norm_num) (sr 1 173495 260243 (by norm_num) (by norm_num) (sr 1 260243 390365 (by norm_num) (by norm_num) (sr 3 390365 146387 (by norm_num) (by norm_num) (sr 1 146387 219581 (by norm_num) (by norm_num) (sr 3 219581 82343 (by norm_num) (by norm_num) (B 82343 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R102815 : Reach 102815 := (sr 1 102815 154223 (by norm_num) (by norm_num) (sr 1 154223 231335 (by norm_num) (by norm_num) (sr 1 231335 347003 (by norm_num) (by norm_num) (sr 1 347003 520505 (by norm_num) (by norm_num) (sr 2 520505 390379 (by norm_num) (by norm_num) (sr 1 390379 585569 (by norm_num) (by norm_num) (sr 2 585569 439177 (by norm_num) (by norm_num) (sr 2 439177 329383 (by norm_num) (by norm_num) (sr 1 329383 494075 (by norm_num) (by norm_num) (sr 1 494075 741113 (by norm_num) (by norm_num) (sr 2 741113 555835 (by norm_num) (by norm_num) (sr 1 555835 833753 (by norm_num) (by norm_num) (sr 2 833753 625315 (by norm_num) (by norm_num) (sr 1 625315 937973 (by norm_num) (by norm_num) (sr 5 937973 87935 (by norm_num) (by norm_num) (B 87935 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R102819 : Reach 102819 := (sr 1 102819 154229 (by norm_num) (by norm_num) (sr 5 154229 14459 (by norm_num) (by norm_num) (B 14459 (by norm_num) (by norm_num) (by norm_num))))
theorem R102823 : Reach 102823 := (sr 1 102823 154235 (by norm_num) (by norm_num) (sr 1 154235 231353 (by norm_num) (by norm_num) (sr 2 231353 173515 (by norm_num) (by norm_num) (sr 1 173515 260273 (by norm_num) (by norm_num) (sr 2 260273 195205 (by norm_num) (by norm_num) (sr 4 195205 36601 (by norm_num) (by norm_num) (B 36601 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R102827 : Reach 102827 := (sr 1 102827 154241 (by norm_num) (by norm_num) (sr 2 154241 115681 (by norm_num) (by norm_num) (sr 2 115681 86761 (by norm_num) (by norm_num) (B 86761 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102831 : Reach 102831 := (sr 1 102831 154247 (by norm_num) (by norm_num) (sr 1 154247 231371 (by norm_num) (by norm_num) (sr 1 231371 347057 (by norm_num) (by norm_num) (sr 2 347057 260293 (by norm_num) (by norm_num) (sr 4 260293 48805 (by norm_num) (by norm_num) (B 48805 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102835 : Reach 102835 := (sr 1 102835 154253 (by norm_num) (by norm_num) (sr 3 154253 57845 (by norm_num) (by norm_num) (B 57845 (by norm_num) (by norm_num) (by norm_num))))
theorem R102839 : Reach 102839 := (sr 1 102839 154259 (by norm_num) (by norm_num) (sr 1 154259 231389 (by norm_num) (by norm_num) (sr 3 231389 86771 (by norm_num) (by norm_num) (B 86771 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102843 : Reach 102843 := (sr 1 102843 154265 (by norm_num) (by norm_num) (sr 2 154265 115699 (by norm_num) (by norm_num) (sr 1 115699 173549 (by norm_num) (by norm_num) (sr 3 173549 65081 (by norm_num) (by norm_num) (B 65081 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102847 : Reach 102847 := (sr 1 102847 154271 (by norm_num) (by norm_num) (sr 1 154271 231407 (by norm_num) (by norm_num) (sr 1 231407 347111 (by norm_num) (by norm_num) (sr 1 347111 520667 (by norm_num) (by norm_num) (sr 1 520667 781001 (by norm_num) (by norm_num) (sr 2 781001 585751 (by norm_num) (by norm_num) (sr 1 585751 878627 (by norm_num) (by norm_num) (sr 1 878627 1317941 (by norm_num) (by norm_num) (sr 5 1317941 123557 (by norm_num) (by norm_num) (sr 4 123557 23167 (by norm_num) (by norm_num) (B 23167 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R102851 : Reach 102851 := (sr 1 102851 154277 (by norm_num) (by norm_num) (sr 4 154277 28927 (by norm_num) (by norm_num) (B 28927 (by norm_num) (by norm_num) (by norm_num))))
theorem R102855 : Reach 102855 := (sr 1 102855 154283 (by norm_num) (by norm_num) (sr 1 154283 231425 (by norm_num) (by norm_num) (sr 2 231425 173569 (by norm_num) (by norm_num) (sr 2 173569 130177 (by norm_num) (by norm_num) (sr 2 130177 97633 (by norm_num) (by norm_num) (B 97633 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102859 : Reach 102859 := (sr 1 102859 154289 (by norm_num) (by norm_num) (sr 2 154289 115717 (by norm_num) (by norm_num) (sr 4 115717 21697 (by norm_num) (by norm_num) (B 21697 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102863 : Reach 102863 := (sr 1 102863 154295 (by norm_num) (by norm_num) (sr 1 154295 231443 (by norm_num) (by norm_num) (sr 1 231443 347165 (by norm_num) (by norm_num) (sr 3 347165 130187 (by norm_num) (by norm_num) (sr 1 130187 195281 (by norm_num) (by norm_num) (sr 2 195281 146461 (by norm_num) (by norm_num) (sr 3 146461 54923 (by norm_num) (by norm_num) (B 54923 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R102867 : Reach 102867 := (sr 1 102867 154301 (by norm_num) (by norm_num) (sr 3 154301 57863 (by norm_num) (by norm_num) (B 57863 (by norm_num) (by norm_num) (by norm_num))))
theorem R102871 : Reach 102871 := (sr 1 102871 154307 (by norm_num) (by norm_num) (sr 1 154307 231461 (by norm_num) (by norm_num) (sr 4 231461 43399 (by norm_num) (by norm_num) (B 43399 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102875 : Reach 102875 := (sr 1 102875 154313 (by norm_num) (by norm_num) (sr 2 154313 115735 (by norm_num) (by norm_num) (sr 1 115735 173603 (by norm_num) (by norm_num) (sr 1 173603 260405 (by norm_num) (by norm_num) (sr 5 260405 24413 (by norm_num) (by norm_num) (B 24413 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102879 : Reach 102879 := (sr 1 102879 154319 (by norm_num) (by norm_num) (sr 1 154319 231479 (by norm_num) (by norm_num) (sr 1 231479 347219 (by norm_num) (by norm_num) (sr 1 347219 520829 (by norm_num) (by norm_num) (sr 3 520829 195311 (by norm_num) (by norm_num) (sr 1 195311 292967 (by norm_num) (by norm_num) (sr 1 292967 439451 (by norm_num) (by norm_num) (sr 1 439451 659177 (by norm_num) (by norm_num) (sr 2 659177 494383 (by norm_num) (by norm_num) (sr 1 494383 741575 (by norm_num) (by norm_num) (sr 1 741575 1112363 (by norm_num) (by norm_num) (sr 1 1112363 1668545 (by norm_num) (by norm_num) (sr 2 1668545 1251409 (by norm_num) (by norm_num) (sr 2 1251409 938557 (by norm_num) (by norm_num) (sr 3 938557 351959 (by norm_num) (by norm_num) (sr 1 351959 527939 (by norm_num) (by norm_num) (sr 1 527939 791909 (by norm_num) (by norm_num) (sr 4 791909 148483 (by norm_num) (by norm_num) (sr 1 148483 222725 (by norm_num) (by norm_num) (sr 4 222725 41761 (by norm_num) (by norm_num) (B 41761 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))
theorem R102883 : Reach 102883 := (sr 1 102883 154325 (by norm_num) (by norm_num) (sr 7 154325 3617 (by norm_num) (by norm_num) (B 3617 (by norm_num) (by norm_num) (by norm_num))))
theorem R102887 : Reach 102887 := (sr 1 102887 154331 (by norm_num) (by norm_num) (sr 1 154331 231497 (by norm_num) (by norm_num) (sr 2 231497 173623 (by norm_num) (by norm_num) (sr 1 173623 260435 (by norm_num) (by norm_num) (sr 1 260435 390653 (by norm_num) (by norm_num) (sr 3 390653 146495 (by norm_num) (by norm_num) (sr 1 146495 219743 (by norm_num) (by norm_num) (sr 1 219743 329615 (by norm_num) (by norm_num) (sr 1 329615 494423 (by norm_num) (by norm_num) (sr 1 494423 741635 (by norm_num) (by norm_num) (sr 1 741635 1112453 (by norm_num) (by norm_num) (sr 4 1112453 208585 (by norm_num) (by norm_num) (sr 2 208585 156439 (by norm_num) (by norm_num) (sr 1 156439 234659 (by norm_num) (by norm_num) (sr 1 234659 351989 (by norm_num) (by norm_num) (sr 5 351989 32999 (by norm_num) (by norm_num) (B 32999 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))
theorem R102891 : Reach 102891 := (sr 1 102891 154337 (by norm_num) (by norm_num) (sr 2 154337 115753 (by norm_num) (by norm_num) (sr 2 115753 86815 (by norm_num) (by norm_num) (B 86815 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102895 : Reach 102895 := (sr 1 102895 154343 (by norm_num) (by norm_num) (sr 1 154343 231515 (by norm_num) (by norm_num) (sr 1 231515 347273 (by norm_num) (by norm_num) (sr 2 347273 260455 (by norm_num) (by norm_num) (sr 1 260455 390683 (by norm_num) (by norm_num) (sr 1 390683 586025 (by norm_num) (by norm_num) (sr 2 586025 439519 (by norm_num) (by norm_num) (sr 1 439519 659279 (by norm_num) (by norm_num) (sr 1 659279 988919 (by norm_num) (by norm_num) (sr 1 988919 1483379 (by norm_num) (by norm_num) (sr 1 1483379 2225069 (by norm_num) (by norm_num) (sr 3 2225069 834401 (by norm_num) (by norm_num) (sr 2 834401 625801 (by norm_num) (by norm_num) (sr 2 625801 469351 (by norm_num) (by norm_num) (sr 1 469351 704027 (by norm_num) (by norm_num) (sr 1 704027 1056041 (by norm_num) (by norm_num) (sr 2 1056041 792031 (by norm_num) (by norm_num) (sr 1 792031 1188047 (by norm_num) (by norm_num) (sr 1 1188047 1782071 (by norm_num) (by norm_num) (sr 1 1782071 2673107 (by norm_num) (by norm_num) (sr 1 2673107 4009661 (by norm_num) (by norm_num) (sr 3 4009661 1503623 (by norm_num) (by norm_num) (sr 1 1503623 2255435 (by norm_num) (by norm_num) (sr 1 2255435 3383153 (by norm_num) (by norm_num) (sr 2 3383153 2537365 (by norm_num) (by norm_num) (sr 6 2537365 118939 (by norm_num) (by norm_num) (sr 1 118939 178409 (by norm_num) (by norm_num) (sr 2 178409 133807 (by norm_num) (by norm_num) (sr 1 133807 200711 (by norm_num) (by norm_num) (sr 1 200711 301067 (by norm_num) (by norm_num) (sr 1 301067 451601 (by norm_num) (by norm_num) (sr 2 451601 338701 (by norm_num) (by norm_num) (sr 3 338701 127013 (by norm_num) (by norm_num) (sr 4 127013 23815 (by norm_num) (by norm_num) (B 23815 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))))))))
theorem R102899 : Reach 102899 := (sr 1 102899 154349 (by norm_num) (by norm_num) (sr 3 154349 57881 (by norm_num) (by norm_num) (B 57881 (by norm_num) (by norm_num) (by norm_num))))
theorem R102903 : Reach 102903 := (sr 1 102903 154355 (by norm_num) (by norm_num) (sr 1 154355 231533 (by norm_num) (by norm_num) (sr 3 231533 86825 (by norm_num) (by norm_num) (B 86825 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102907 : Reach 102907 := (sr 1 102907 154361 (by norm_num) (by norm_num) (sr 2 154361 115771 (by norm_num) (by norm_num) (sr 1 115771 173657 (by norm_num) (by norm_num) (sr 2 173657 130243 (by norm_num) (by norm_num) (sr 1 130243 195365 (by norm_num) (by norm_num) (sr 4 195365 36631 (by norm_num) (by norm_num) (B 36631 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R102911 : Reach 102911 := (sr 1 102911 154367 (by norm_num) (by norm_num) (sr 1 154367 231551 (by norm_num) (by norm_num) (sr 1 231551 347327 (by norm_num) (by norm_num) (sr 1 347327 520991 (by norm_num) (by norm_num) (sr 1 520991 781487 (by norm_num) (by norm_num) (sr 1 781487 1172231 (by norm_num) (by norm_num) (sr 1 1172231 1758347 (by norm_num) (by norm_num) (sr 1 1758347 2637521 (by norm_num) (by norm_num) (sr 2 2637521 1978141 (by norm_num) (by norm_num) (sr 3 1978141 741803 (by norm_num) (by norm_num) (sr 1 741803 1112705 (by norm_num) (by norm_num) (sr 2 1112705 834529 (by norm_num) (by norm_num) (sr 2 834529 625897 (by norm_num) (by norm_num) (sr 2 625897 469423 (by norm_num) (by norm_num) (sr 1 469423 704135 (by norm_num) (by norm_num) (sr 1 704135 1056203 (by norm_num) (by norm_num) (sr 1 1056203 1584305 (by norm_num) (by norm_num) (sr 2 1584305 1188229 (by norm_num) (by norm_num) (sr 4 1188229 222793 (by norm_num) (by norm_num) (sr 2 222793 167095 (by norm_num) (by norm_num) (sr 1 167095 250643 (by norm_num) (by norm_num) (sr 1 250643 375965 (by norm_num) (by norm_num) (sr 3 375965 140987 (by norm_num) (by norm_num) (sr 1 140987 211481 (by norm_num) (by norm_num) (sr 2 211481 158611 (by norm_num) (by norm_num) (sr 1 158611 237917 (by norm_num) (by norm_num) (sr 3 237917 89219 (by norm_num) (by norm_num) (B 89219 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))
theorem R102915 : Reach 102915 := (sr 1 102915 154373 (by norm_num) (by norm_num) (sr 4 154373 28945 (by norm_num) (by norm_num) (B 28945 (by norm_num) (by norm_num) (by norm_num))))
theorem R102919 : Reach 102919 := (sr 1 102919 154379 (by norm_num) (by norm_num) (sr 1 154379 231569 (by norm_num) (by norm_num) (sr 2 231569 173677 (by norm_num) (by norm_num) (sr 3 173677 65129 (by norm_num) (by norm_num) (B 65129 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102923 : Reach 102923 := (sr 1 102923 154385 (by norm_num) (by norm_num) (sr 2 154385 115789 (by norm_num) (by norm_num) (sr 3 115789 43421 (by norm_num) (by norm_num) (B 43421 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102927 : Reach 102927 := (sr 1 102927 154391 (by norm_num) (by norm_num) (sr 1 154391 231587 (by norm_num) (by norm_num) (sr 1 231587 347381 (by norm_num) (by norm_num) (sr 5 347381 32567 (by norm_num) (by norm_num) (B 32567 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102931 : Reach 102931 := (sr 1 102931 154397 (by norm_num) (by norm_num) (sr 3 154397 57899 (by norm_num) (by norm_num) (B 57899 (by norm_num) (by norm_num) (by norm_num))))
theorem R102935 : Reach 102935 := (sr 1 102935 154403 (by norm_num) (by norm_num) (sr 1 154403 231605 (by norm_num) (by norm_num) (sr 5 231605 21713 (by norm_num) (by norm_num) (B 21713 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102939 : Reach 102939 := (sr 1 102939 154409 (by norm_num) (by norm_num) (sr 2 154409 115807 (by norm_num) (by norm_num) (sr 1 115807 173711 (by norm_num) (by norm_num) (sr 1 173711 260567 (by norm_num) (by norm_num) (sr 1 260567 390851 (by norm_num) (by norm_num) (sr 1 390851 586277 (by norm_num) (by norm_num) (sr 4 586277 109927 (by norm_num) (by norm_num) (sr 1 109927 164891 (by norm_num) (by norm_num) (sr 1 164891 247337 (by norm_num) (by norm_num) (sr 2 247337 185503 (by norm_num) (by norm_num) (sr 1 185503 278255 (by norm_num) (by norm_num) (sr 1 278255 417383 (by norm_num) (by norm_num) (sr 1 417383 626075 (by norm_num) (by norm_num) (sr 1 626075 939113 (by norm_num) (by norm_num) (sr 2 939113 704335 (by norm_num) (by norm_num) (sr 1 704335 1056503 (by norm_num) (by norm_num) (sr 1 1056503 1584755 (by norm_num) (by norm_num) (sr 1 1584755 2377133 (by norm_num) (by norm_num) (sr 3 2377133 891425 (by norm_num) (by norm_num) (sr 2 891425 668569 (by norm_num) (by norm_num) (sr 2 668569 501427 (by norm_num) (by norm_num) (sr 1 501427 752141 (by norm_num) (by norm_num) (sr 3 752141 282053 (by norm_num) (by norm_num) (sr 4 282053 52885 (by norm_num) (by norm_num) (B 52885 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))
theorem R102943 : Reach 102943 := (sr 1 102943 154415 (by norm_num) (by norm_num) (sr 1 154415 231623 (by norm_num) (by norm_num) (sr 1 231623 347435 (by norm_num) (by norm_num) (sr 1 347435 521153 (by norm_num) (by norm_num) (sr 2 521153 390865 (by norm_num) (by norm_num) (sr 2 390865 293149 (by norm_num) (by norm_num) (sr 3 293149 109931 (by norm_num) (by norm_num) (sr 1 109931 164897 (by norm_num) (by norm_num) (sr 2 164897 123673 (by norm_num) (by norm_num) (sr 2 123673 92755 (by norm_num) (by norm_num) (B 92755 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R102947 : Reach 102947 := (sr 1 102947 154421 (by norm_num) (by norm_num) (sr 5 154421 14477 (by norm_num) (by norm_num) (B 14477 (by norm_num) (by norm_num) (by norm_num))))
theorem R102951 : Reach 102951 := (sr 1 102951 154427 (by norm_num) (by norm_num) (sr 1 154427 231641 (by norm_num) (by norm_num) (sr 2 231641 173731 (by norm_num) (by norm_num) (sr 1 173731 260597 (by norm_num) (by norm_num) (sr 5 260597 24431 (by norm_num) (by norm_num) (B 24431 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102955 : Reach 102955 := (sr 1 102955 154433 (by norm_num) (by norm_num) (sr 2 154433 115825 (by norm_num) (by norm_num) (sr 2 115825 86869 (by norm_num) (by norm_num) (B 86869 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102959 : Reach 102959 := (sr 1 102959 154439 (by norm_num) (by norm_num) (sr 1 154439 231659 (by norm_num) (by norm_num) (sr 1 231659 347489 (by norm_num) (by norm_num) (sr 2 347489 260617 (by norm_num) (by norm_num) (sr 2 260617 195463 (by norm_num) (by norm_num) (sr 1 195463 293195 (by norm_num) (by norm_num) (sr 1 293195 439793 (by norm_num) (by norm_num) (sr 2 439793 329845 (by norm_num) (by norm_num) (sr 5 329845 30923 (by norm_num) (by norm_num) (B 30923 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R102963 : Reach 102963 := (sr 1 102963 154445 (by norm_num) (by norm_num) (sr 3 154445 57917 (by norm_num) (by norm_num) (B 57917 (by norm_num) (by norm_num) (by norm_num))))
theorem R102967 : Reach 102967 := (sr 1 102967 154451 (by norm_num) (by norm_num) (sr 1 154451 231677 (by norm_num) (by norm_num) (sr 3 231677 86879 (by norm_num) (by norm_num) (B 86879 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102971 : Reach 102971 := (sr 1 102971 154457 (by norm_num) (by norm_num) (sr 2 154457 115843 (by norm_num) (by norm_num) (sr 1 115843 173765 (by norm_num) (by norm_num) (sr 4 173765 32581 (by norm_num) (by norm_num) (B 32581 (by norm_num) (by norm_num) (by norm_num))))))
theorem R102975 : Reach 102975 := (sr 1 102975 154463 (by norm_num) (by norm_num) (sr 1 154463 231695 (by norm_num) (by norm_num) (sr 1 231695 347543 (by norm_num) (by norm_num) (sr 1 347543 521315 (by norm_num) (by norm_num) (sr 1 521315 781973 (by norm_num) (by norm_num) (sr 6 781973 36655 (by norm_num) (by norm_num) (B 36655 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R102979 : Reach 102979 := (sr 1 102979 154469 (by norm_num) (by norm_num) (sr 4 154469 28963 (by norm_num) (by norm_num) (B 28963 (by norm_num) (by norm_num) (by norm_num))))
theorem R102983 : Reach 102983 := (sr 1 102983 154475 (by norm_num) (by norm_num) (sr 1 154475 231713 (by norm_num) (by norm_num) (sr 2 231713 173785 (by norm_num) (by norm_num) (sr 2 173785 130339 (by norm_num) (by norm_num) (sr 1 130339 195509 (by norm_num) (by norm_num) (sr 5 195509 18329 (by norm_num) (by norm_num) (B 18329 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R102987 : Reach 102987 := (sr 1 102987 154481 (by norm_num) (by norm_num) (sr 2 154481 115861 (by norm_num) (by norm_num) (sr 6 115861 5431 (by norm_num) (by norm_num) (B 5431 (by norm_num) (by norm_num) (by norm_num)))))
theorem R102991 : Reach 102991 := (sr 1 102991 154487 (by norm_num) (by norm_num) (sr 1 154487 231731 (by norm_num) (by norm_num) (sr 1 231731 347597 (by norm_num) (by norm_num) (sr 3 347597 130349 (by norm_num) (by norm_num) (sr 3 130349 48881 (by norm_num) (by norm_num) (B 48881 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R102995 : Reach 102995 := (sr 1 102995 154493 (by norm_num) (by norm_num) (sr 3 154493 57935 (by norm_num) (by norm_num) (B 57935 (by norm_num) (by norm_num) (by norm_num))))
theorem R102999 : Reach 102999 := (sr 1 102999 154499 (by norm_num) (by norm_num) (sr 1 154499 231749 (by norm_num) (by norm_num) (sr 4 231749 43453 (by norm_num) (by norm_num) (B 43453 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103003 : Reach 103003 := (sr 1 103003 154505 (by norm_num) (by norm_num) (sr 2 154505 115879 (by norm_num) (by norm_num) (sr 1 115879 173819 (by norm_num) (by norm_num) (sr 1 173819 260729 (by norm_num) (by norm_num) (sr 2 260729 195547 (by norm_num) (by norm_num) (sr 1 195547 293321 (by norm_num) (by norm_num) (sr 2 293321 219991 (by norm_num) (by norm_num) (sr 1 219991 329987 (by norm_num) (by norm_num) (sr 1 329987 494981 (by norm_num) (by norm_num) (sr 4 494981 92809 (by norm_num) (by norm_num) (B 92809 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R103007 : Reach 103007 := (sr 1 103007 154511 (by norm_num) (by norm_num) (sr 1 154511 231767 (by norm_num) (by norm_num) (sr 1 231767 347651 (by norm_num) (by norm_num) (sr 1 347651 521477 (by norm_num) (by norm_num) (sr 4 521477 97777 (by norm_num) (by norm_num) (B 97777 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103011 : Reach 103011 := (sr 1 103011 154517 (by norm_num) (by norm_num) (sr 6 154517 7243 (by norm_num) (by norm_num) (B 7243 (by norm_num) (by norm_num) (by norm_num))))
theorem R103015 : Reach 103015 := (sr 1 103015 154523 (by norm_num) (by norm_num) (sr 1 154523 231785 (by norm_num) (by norm_num) (sr 2 231785 173839 (by norm_num) (by norm_num) (sr 1 173839 260759 (by norm_num) (by norm_num) (sr 1 260759 391139 (by norm_num) (by norm_num) (sr 1 391139 586709 (by norm_num) (by norm_num) (sr 7 586709 13751 (by norm_num) (by norm_num) (B 13751 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R103019 : Reach 103019 := (sr 1 103019 154529 (by norm_num) (by norm_num) (sr 2 154529 115897 (by norm_num) (by norm_num) (sr 2 115897 86923 (by norm_num) (by norm_num) (B 86923 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103023 : Reach 103023 := (sr 1 103023 154535 (by norm_num) (by norm_num) (sr 1 154535 231803 (by norm_num) (by norm_num) (sr 1 231803 347705 (by norm_num) (by norm_num) (sr 2 347705 260779 (by norm_num) (by norm_num) (sr 1 260779 391169 (by norm_num) (by norm_num) (sr 2 391169 293377 (by norm_num) (by norm_num) (sr 2 293377 220033 (by norm_num) (by norm_num) (sr 2 220033 165025 (by norm_num) (by norm_num) (sr 2 165025 123769 (by norm_num) (by norm_num) (sr 2 123769 92827 (by norm_num) (by norm_num) (B 92827 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R103027 : Reach 103027 := (sr 1 103027 154541 (by norm_num) (by norm_num) (sr 3 154541 57953 (by norm_num) (by norm_num) (B 57953 (by norm_num) (by norm_num) (by norm_num))))
theorem R103031 : Reach 103031 := (sr 1 103031 154547 (by norm_num) (by norm_num) (sr 1 154547 231821 (by norm_num) (by norm_num) (sr 3 231821 86933 (by norm_num) (by norm_num) (B 86933 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103035 : Reach 103035 := (sr 1 103035 154553 (by norm_num) (by norm_num) (sr 2 154553 115915 (by norm_num) (by norm_num) (sr 1 115915 173873 (by norm_num) (by norm_num) (sr 2 173873 130405 (by norm_num) (by norm_num) (sr 4 130405 24451 (by norm_num) (by norm_num) (B 24451 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103039 : Reach 103039 := (sr 1 103039 154559 (by norm_num) (by norm_num) (sr 1 154559 231839 (by norm_num) (by norm_num) (sr 1 231839 347759 (by norm_num) (by norm_num) (sr 1 347759 521639 (by norm_num) (by norm_num) (sr 1 521639 782459 (by norm_num) (by norm_num) (sr 1 782459 1173689 (by norm_num) (by norm_num) (sr 2 1173689 880267 (by norm_num) (by norm_num) (sr 1 880267 1320401 (by norm_num) (by norm_num) (sr 2 1320401 990301 (by norm_num) (by norm_num) (sr 3 990301 371363 (by norm_num) (by norm_num) (sr 1 371363 557045 (by norm_num) (by norm_num) (sr 5 557045 52223 (by norm_num) (by norm_num) (B 52223 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R103043 : Reach 103043 := (sr 1 103043 154565 (by norm_num) (by norm_num) (sr 4 154565 28981 (by norm_num) (by norm_num) (B 28981 (by norm_num) (by norm_num) (by norm_num))))
theorem R103047 : Reach 103047 := (sr 1 103047 154571 (by norm_num) (by norm_num) (sr 1 154571 231857 (by norm_num) (by norm_num) (sr 2 231857 173893 (by norm_num) (by norm_num) (sr 4 173893 32605 (by norm_num) (by norm_num) (B 32605 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103051 : Reach 103051 := (sr 1 103051 154577 (by norm_num) (by norm_num) (sr 2 154577 115933 (by norm_num) (by norm_num) (sr 3 115933 43475 (by norm_num) (by norm_num) (B 43475 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103055 : Reach 103055 := (sr 1 103055 154583 (by norm_num) (by norm_num) (sr 1 154583 231875 (by norm_num) (by norm_num) (sr 1 231875 347813 (by norm_num) (by norm_num) (sr 4 347813 65215 (by norm_num) (by norm_num) (B 65215 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103059 : Reach 103059 := (sr 1 103059 154589 (by norm_num) (by norm_num) (sr 3 154589 57971 (by norm_num) (by norm_num) (B 57971 (by norm_num) (by norm_num) (by norm_num))))
theorem R103063 : Reach 103063 := (sr 1 103063 154595 (by norm_num) (by norm_num) (sr 1 154595 231893 (by norm_num) (by norm_num) (sr 7 231893 5435 (by norm_num) (by norm_num) (B 5435 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103067 : Reach 103067 := (sr 1 103067 154601 (by norm_num) (by norm_num) (sr 2 154601 115951 (by norm_num) (by norm_num) (sr 1 115951 173927 (by norm_num) (by norm_num) (sr 1 173927 260891 (by norm_num) (by norm_num) (sr 1 260891 391337 (by norm_num) (by norm_num) (sr 2 391337 293503 (by norm_num) (by norm_num) (sr 1 293503 440255 (by norm_num) (by norm_num) (sr 1 440255 660383 (by norm_num) (by norm_num) (sr 1 660383 990575 (by norm_num) (by norm_num) (sr 1 990575 1485863 (by norm_num) (by norm_num) (sr 1 1485863 2228795 (by norm_num) (by norm_num) (sr 1 2228795 3343193 (by norm_num) (by norm_num) (sr 2 3343193 2507395 (by norm_num) (by norm_num) (sr 1 2507395 3761093 (by norm_num) (by norm_num) (sr 4 3761093 705205 (by norm_num) (by norm_num) (sr 5 705205 66113 (by norm_num) (by norm_num) (B 66113 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))
theorem R103071 : Reach 103071 := (sr 1 103071 154607 (by norm_num) (by norm_num) (sr 1 154607 231911 (by norm_num) (by norm_num) (sr 1 231911 347867 (by norm_num) (by norm_num) (sr 1 347867 521801 (by norm_num) (by norm_num) (sr 2 521801 391351 (by norm_num) (by norm_num) (sr 1 391351 587027 (by norm_num) (by norm_num) (sr 1 587027 880541 (by norm_num) (by norm_num) (sr 3 880541 330203 (by norm_num) (by norm_num) (sr 1 330203 495305 (by norm_num) (by norm_num) (sr 2 495305 371479 (by norm_num) (by norm_num) (sr 1 371479 557219 (by norm_num) (by norm_num) (sr 1 557219 835829 (by norm_num) (by norm_num) (sr 5 835829 78359 (by norm_num) (by norm_num) (B 78359 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R103075 : Reach 103075 := (sr 1 103075 154613 (by norm_num) (by norm_num) (sr 5 154613 14495 (by norm_num) (by norm_num) (B 14495 (by norm_num) (by norm_num) (by norm_num))))
theorem R103079 : Reach 103079 := (sr 1 103079 154619 (by norm_num) (by norm_num) (sr 1 154619 231929 (by norm_num) (by norm_num) (sr 2 231929 173947 (by norm_num) (by norm_num) (sr 1 173947 260921 (by norm_num) (by norm_num) (sr 2 260921 195691 (by norm_num) (by norm_num) (sr 1 195691 293537 (by norm_num) (by norm_num) (sr 2 293537 220153 (by norm_num) (by norm_num) (sr 2 220153 165115 (by norm_num) (by norm_num) (sr 1 165115 247673 (by norm_num) (by norm_num) (sr 2 247673 185755 (by norm_num) (by norm_num) (sr 1 185755 278633 (by norm_num) (by norm_num) (sr 2 278633 208975 (by norm_num) (by norm_num) (sr 1 208975 313463 (by norm_num) (by norm_num) (sr 1 313463 470195 (by norm_num) (by norm_num) (sr 1 470195 705293 (by norm_num) (by norm_num) (sr 3 705293 264485 (by norm_num) (by norm_num) (sr 4 264485 49591 (by norm_num) (by norm_num) (B 49591 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))
theorem R103083 : Reach 103083 := (sr 1 103083 154625 (by norm_num) (by norm_num) (sr 2 154625 115969 (by norm_num) (by norm_num) (sr 2 115969 86977 (by norm_num) (by norm_num) (B 86977 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103087 : Reach 103087 := (sr 1 103087 154631 (by norm_num) (by norm_num) (sr 1 154631 231947 (by norm_num) (by norm_num) (sr 1 231947 347921 (by norm_num) (by norm_num) (sr 2 347921 260941 (by norm_num) (by norm_num) (sr 3 260941 97853 (by norm_num) (by norm_num) (B 97853 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103091 : Reach 103091 := (sr 1 103091 154637 (by norm_num) (by norm_num) (sr 3 154637 57989 (by norm_num) (by norm_num) (B 57989 (by norm_num) (by norm_num) (by norm_num))))
theorem R103095 : Reach 103095 := (sr 1 103095 154643 (by norm_num) (by norm_num) (sr 1 154643 231965 (by norm_num) (by norm_num) (sr 3 231965 86987 (by norm_num) (by norm_num) (B 86987 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103099 : Reach 103099 := (sr 1 103099 154649 (by norm_num) (by norm_num) (sr 2 154649 115987 (by norm_num) (by norm_num) (sr 1 115987 173981 (by norm_num) (by norm_num) (sr 3 173981 65243 (by norm_num) (by norm_num) (B 65243 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103103 : Reach 103103 := (sr 1 103103 154655 (by norm_num) (by norm_num) (sr 1 154655 231983 (by norm_num) (by norm_num) (sr 1 231983 347975 (by norm_num) (by norm_num) (sr 1 347975 521963 (by norm_num) (by norm_num) (sr 1 521963 782945 (by norm_num) (by norm_num) (sr 2 782945 587209 (by norm_num) (by norm_num) (sr 2 587209 440407 (by norm_num) (by norm_num) (sr 1 440407 660611 (by norm_num) (by norm_num) (sr 1 660611 990917 (by norm_num) (by norm_num) (sr 4 990917 185797 (by norm_num) (by norm_num) (sr 4 185797 34837 (by norm_num) (by norm_num) (B 34837 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R103107 : Reach 103107 := (sr 1 103107 154661 (by norm_num) (by norm_num) (sr 4 154661 28999 (by norm_num) (by norm_num) (B 28999 (by norm_num) (by norm_num) (by norm_num))))
theorem R103111 : Reach 103111 := (sr 1 103111 154667 (by norm_num) (by norm_num) (sr 1 154667 232001 (by norm_num) (by norm_num) (sr 2 232001 174001 (by norm_num) (by norm_num) (sr 2 174001 130501 (by norm_num) (by norm_num) (sr 4 130501 24469 (by norm_num) (by norm_num) (B 24469 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103115 : Reach 103115 := (sr 1 103115 154673 (by norm_num) (by norm_num) (sr 2 154673 116005 (by norm_num) (by norm_num) (sr 4 116005 21751 (by norm_num) (by norm_num) (B 21751 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103119 : Reach 103119 := (sr 1 103119 154679 (by norm_num) (by norm_num) (sr 1 154679 232019 (by norm_num) (by norm_num) (sr 1 232019 348029 (by norm_num) (by norm_num) (sr 3 348029 130511 (by norm_num) (by norm_num) (sr 1 130511 195767 (by norm_num) (by norm_num) (sr 1 195767 293651 (by norm_num) (by norm_num) (sr 1 293651 440477 (by norm_num) (by norm_num) (sr 3 440477 165179 (by norm_num) (by norm_num) (sr 1 165179 247769 (by norm_num) (by norm_num) (sr 2 247769 185827 (by norm_num) (by norm_num) (sr 1 185827 278741 (by norm_num) (by norm_num) (sr 7 278741 6533 (by norm_num) (by norm_num) (B 6533 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R103123 : Reach 103123 := (sr 1 103123 154685 (by norm_num) (by norm_num) (sr 3 154685 58007 (by norm_num) (by norm_num) (B 58007 (by norm_num) (by norm_num) (by norm_num))))
theorem R103127 : Reach 103127 := (sr 1 103127 154691 (by norm_num) (by norm_num) (sr 1 154691 232037 (by norm_num) (by norm_num) (sr 4 232037 43507 (by norm_num) (by norm_num) (B 43507 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103131 : Reach 103131 := (sr 1 103131 154697 (by norm_num) (by norm_num) (sr 2 154697 116023 (by norm_num) (by norm_num) (sr 1 116023 174035 (by norm_num) (by norm_num) (sr 1 174035 261053 (by norm_num) (by norm_num) (sr 3 261053 97895 (by norm_num) (by norm_num) (B 97895 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103135 : Reach 103135 := (sr 1 103135 154703 (by norm_num) (by norm_num) (sr 1 154703 232055 (by norm_num) (by norm_num) (sr 1 232055 348083 (by norm_num) (by norm_num) (sr 1 348083 522125 (by norm_num) (by norm_num) (sr 3 522125 195797 (by norm_num) (by norm_num) (sr 7 195797 4589 (by norm_num) (by norm_num) (B 4589 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R103139 : Reach 103139 := (sr 1 103139 154709 (by norm_num) (by norm_num) (sr 8 154709 1813 (by norm_num) (by norm_num) (B 1813 (by norm_num) (by norm_num) (by norm_num))))
theorem R103143 : Reach 103143 := (sr 1 103143 154715 (by norm_num) (by norm_num) (sr 1 154715 232073 (by norm_num) (by norm_num) (sr 2 232073 174055 (by norm_num) (by norm_num) (sr 1 174055 261083 (by norm_num) (by norm_num) (sr 1 261083 391625 (by norm_num) (by norm_num) (sr 2 391625 293719 (by norm_num) (by norm_num) (sr 1 293719 440579 (by norm_num) (by norm_num) (sr 1 440579 660869 (by norm_num) (by norm_num) (sr 4 660869 123913 (by norm_num) (by norm_num) (sr 2 123913 92935 (by norm_num) (by norm_num) (B 92935 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R103147 : Reach 103147 := (sr 1 103147 154721 (by norm_num) (by norm_num) (sr 2 154721 116041 (by norm_num) (by norm_num) (sr 2 116041 87031 (by norm_num) (by norm_num) (B 87031 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103151 : Reach 103151 := (sr 1 103151 154727 (by norm_num) (by norm_num) (sr 1 154727 232091 (by norm_num) (by norm_num) (sr 1 232091 348137 (by norm_num) (by norm_num) (sr 2 348137 261103 (by norm_num) (by norm_num) (sr 1 261103 391655 (by norm_num) (by norm_num) (sr 1 391655 587483 (by norm_num) (by norm_num) (sr 1 587483 881225 (by norm_num) (by norm_num) (sr 2 881225 660919 (by norm_num) (by norm_num) (sr 1 660919 991379 (by norm_num) (by norm_num) (sr 1 991379 1487069 (by norm_num) (by norm_num) (sr 3 1487069 557651 (by norm_num) (by norm_num) (sr 1 557651 836477 (by norm_num) (by norm_num) (sr 3 836477 313679 (by norm_num) (by norm_num) (sr 1 313679 470519 (by norm_num) (by norm_num) (sr 1 470519 705779 (by norm_num) (by norm_num) (sr 1 705779 1058669 (by norm_num) (by norm_num) (sr 3 1058669 397001 (by norm_num) (by norm_num) (sr 2 397001 297751 (by norm_num) (by norm_num) (sr 1 297751 446627 (by norm_num) (by norm_num) (sr 1 446627 669941 (by norm_num) (by norm_num) (sr 5 669941 62807 (by norm_num) (by norm_num) (B 62807 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))
theorem R103155 : Reach 103155 := (sr 1 103155 154733 (by norm_num) (by norm_num) (sr 3 154733 58025 (by norm_num) (by norm_num) (B 58025 (by norm_num) (by norm_num) (by norm_num))))
theorem R103159 : Reach 103159 := (sr 1 103159 154739 (by norm_num) (by norm_num) (sr 1 154739 232109 (by norm_num) (by norm_num) (sr 3 232109 87041 (by norm_num) (by norm_num) (B 87041 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103163 : Reach 103163 := (sr 1 103163 154745 (by norm_num) (by norm_num) (sr 2 154745 116059 (by norm_num) (by norm_num) (sr 1 116059 174089 (by norm_num) (by norm_num) (sr 2 174089 130567 (by norm_num) (by norm_num) (sr 1 130567 195851 (by norm_num) (by norm_num) (sr 1 195851 293777 (by norm_num) (by norm_num) (sr 2 293777 220333 (by norm_num) (by norm_num) (sr 3 220333 82625 (by norm_num) (by norm_num) (B 82625 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R103167 : Reach 103167 := (sr 1 103167 154751 (by norm_num) (by norm_num) (sr 1 154751 232127 (by norm_num) (by norm_num) (sr 1 232127 348191 (by norm_num) (by norm_num) (sr 1 348191 522287 (by norm_num) (by norm_num) (sr 1 522287 783431 (by norm_num) (by norm_num) (sr 1 783431 1175147 (by norm_num) (by norm_num) (sr 1 1175147 1762721 (by norm_num) (by norm_num) (sr 2 1762721 1322041 (by norm_num) (by norm_num) (sr 2 1322041 991531 (by norm_num) (by norm_num) (sr 1 991531 1487297 (by norm_num) (by norm_num) (sr 2 1487297 1115473 (by norm_num) (by norm_num) (sr 2 1115473 836605 (by norm_num) (by norm_num) (sr 3 836605 313727 (by norm_num) (by norm_num) (sr 1 313727 470591 (by norm_num) (by norm_num) (sr 1 470591 705887 (by norm_num) (by norm_num) (sr 1 705887 1058831 (by norm_num) (by norm_num) (sr 1 1058831 1588247 (by norm_num) (by norm_num) (sr 1 1588247 2382371 (by norm_num) (by norm_num) (sr 1 2382371 3573557 (by norm_num) (by norm_num) (sr 5 3573557 335021 (by norm_num) (by norm_num) (sr 3 335021 125633 (by norm_num) (by norm_num) (sr 2 125633 94225 (by norm_num) (by norm_num) (B 94225 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R103171 : Reach 103171 := (sr 1 103171 154757 (by norm_num) (by norm_num) (sr 4 154757 29017 (by norm_num) (by norm_num) (B 29017 (by norm_num) (by norm_num) (by norm_num))))
theorem R103175 : Reach 103175 := (sr 1 103175 154763 (by norm_num) (by norm_num) (sr 1 154763 232145 (by norm_num) (by norm_num) (sr 2 232145 174109 (by norm_num) (by norm_num) (sr 3 174109 65291 (by norm_num) (by norm_num) (B 65291 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103179 : Reach 103179 := (sr 1 103179 154769 (by norm_num) (by norm_num) (sr 2 154769 116077 (by norm_num) (by norm_num) (sr 3 116077 43529 (by norm_num) (by norm_num) (B 43529 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103183 : Reach 103183 := (sr 1 103183 154775 (by norm_num) (by norm_num) (sr 1 154775 232163 (by norm_num) (by norm_num) (sr 1 232163 348245 (by norm_num) (by norm_num) (sr 8 348245 4081 (by norm_num) (by norm_num) (B 4081 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103187 : Reach 103187 := (sr 1 103187 154781 (by norm_num) (by norm_num) (sr 3 154781 58043 (by norm_num) (by norm_num) (B 58043 (by norm_num) (by norm_num) (by norm_num))))
theorem R103191 : Reach 103191 := (sr 1 103191 154787 (by norm_num) (by norm_num) (sr 1 154787 232181 (by norm_num) (by norm_num) (sr 5 232181 21767 (by norm_num) (by norm_num) (B 21767 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103195 : Reach 103195 := (sr 1 103195 154793 (by norm_num) (by norm_num) (sr 2 154793 116095 (by norm_num) (by norm_num) (sr 1 116095 174143 (by norm_num) (by norm_num) (sr 1 174143 261215 (by norm_num) (by norm_num) (sr 1 261215 391823 (by norm_num) (by norm_num) (sr 1 391823 587735 (by norm_num) (by norm_num) (sr 1 587735 881603 (by norm_num) (by norm_num) (sr 1 881603 1322405 (by norm_num) (by norm_num) (sr 4 1322405 247951 (by norm_num) (by norm_num) (sr 1 247951 371927 (by norm_num) (by norm_num) (sr 1 371927 557891 (by norm_num) (by norm_num) (sr 1 557891 836837 (by norm_num) (by norm_num) (sr 4 836837 156907 (by norm_num) (by norm_num) (sr 1 156907 235361 (by norm_num) (by norm_num) (sr 2 235361 176521 (by norm_num) (by norm_num) (sr 2 176521 132391 (by norm_num) (by norm_num) (sr 1 132391 198587 (by norm_num) (by norm_num) (sr 1 198587 297881 (by norm_num) (by norm_num) (sr 2 297881 223411 (by norm_num) (by norm_num) (sr 1 223411 335117 (by norm_num) (by norm_num) (sr 3 335117 125669 (by norm_num) (by norm_num) (sr 4 125669 23563 (by norm_num) (by norm_num) (B 23563 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R103199 : Reach 103199 := (sr 1 103199 154799 (by norm_num) (by norm_num) (sr 1 154799 232199 (by norm_num) (by norm_num) (sr 1 232199 348299 (by norm_num) (by norm_num) (sr 1 348299 522449 (by norm_num) (by norm_num) (sr 2 522449 391837 (by norm_num) (by norm_num) (sr 3 391837 146939 (by norm_num) (by norm_num) (sr 1 146939 220409 (by norm_num) (by norm_num) (sr 2 220409 165307 (by norm_num) (by norm_num) (sr 1 165307 247961 (by norm_num) (by norm_num) (sr 2 247961 185971 (by norm_num) (by norm_num) (sr 1 185971 278957 (by norm_num) (by norm_num) (sr 3 278957 104609 (by norm_num) (by norm_num) (sr 2 104609 78457 (by norm_num) (by norm_num) (B 78457 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R103203 : Reach 103203 := (sr 1 103203 154805 (by norm_num) (by norm_num) (sr 5 154805 14513 (by norm_num) (by norm_num) (B 14513 (by norm_num) (by norm_num) (by norm_num))))
theorem R103207 : Reach 103207 := (sr 1 103207 154811 (by norm_num) (by norm_num) (sr 1 154811 232217 (by norm_num) (by norm_num) (sr 2 232217 174163 (by norm_num) (by norm_num) (sr 1 174163 261245 (by norm_num) (by norm_num) (sr 3 261245 97967 (by norm_num) (by norm_num) (B 97967 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103211 : Reach 103211 := (sr 1 103211 154817 (by norm_num) (by norm_num) (sr 2 154817 116113 (by norm_num) (by norm_num) (sr 2 116113 87085 (by norm_num) (by norm_num) (B 87085 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103215 : Reach 103215 := (sr 1 103215 154823 (by norm_num) (by norm_num) (sr 1 154823 232235 (by norm_num) (by norm_num) (sr 1 232235 348353 (by norm_num) (by norm_num) (sr 2 348353 261265 (by norm_num) (by norm_num) (sr 2 261265 195949 (by norm_num) (by norm_num) (sr 3 195949 73481 (by norm_num) (by norm_num) (B 73481 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R103219 : Reach 103219 := (sr 1 103219 154829 (by norm_num) (by norm_num) (sr 3 154829 58061 (by norm_num) (by norm_num) (B 58061 (by norm_num) (by norm_num) (by norm_num))))
theorem R103223 : Reach 103223 := (sr 1 103223 154835 (by norm_num) (by norm_num) (sr 1 154835 232253 (by norm_num) (by norm_num) (sr 3 232253 87095 (by norm_num) (by norm_num) (B 87095 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103227 : Reach 103227 := (sr 1 103227 154841 (by norm_num) (by norm_num) (sr 2 154841 116131 (by norm_num) (by norm_num) (sr 1 116131 174197 (by norm_num) (by norm_num) (sr 5 174197 16331 (by norm_num) (by norm_num) (B 16331 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103231 : Reach 103231 := (sr 1 103231 154847 (by norm_num) (by norm_num) (sr 1 154847 232271 (by norm_num) (by norm_num) (sr 1 232271 348407 (by norm_num) (by norm_num) (sr 1 348407 522611 (by norm_num) (by norm_num) (sr 1 522611 783917 (by norm_num) (by norm_num) (sr 3 783917 293969 (by norm_num) (by norm_num) (sr 2 293969 220477 (by norm_num) (by norm_num) (sr 3 220477 82679 (by norm_num) (by norm_num) (B 82679 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R103235 : Reach 103235 := (sr 1 103235 154853 (by norm_num) (by norm_num) (sr 4 154853 29035 (by norm_num) (by norm_num) (B 29035 (by norm_num) (by norm_num) (by norm_num))))
theorem R103239 : Reach 103239 := (sr 1 103239 154859 (by norm_num) (by norm_num) (sr 1 154859 232289 (by norm_num) (by norm_num) (sr 2 232289 174217 (by norm_num) (by norm_num) (sr 2 174217 130663 (by norm_num) (by norm_num) (sr 1 130663 195995 (by norm_num) (by norm_num) (sr 1 195995 293993 (by norm_num) (by norm_num) (sr 2 293993 220495 (by norm_num) (by norm_num) (sr 1 220495 330743 (by norm_num) (by norm_num) (sr 1 330743 496115 (by norm_num) (by norm_num) (sr 1 496115 744173 (by norm_num) (by norm_num) (sr 3 744173 279065 (by norm_num) (by norm_num) (sr 2 279065 209299 (by norm_num) (by norm_num) (sr 1 209299 313949 (by norm_num) (by norm_num) (sr 3 313949 117731 (by norm_num) (by norm_num) (sr 1 117731 176597 (by norm_num) (by norm_num) (sr 7 176597 4139 (by norm_num) (by norm_num) (B 4139 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))
theorem R103243 : Reach 103243 := (sr 1 103243 154865 (by norm_num) (by norm_num) (sr 2 154865 116149 (by norm_num) (by norm_num) (sr 5 116149 10889 (by norm_num) (by norm_num) (B 10889 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103247 : Reach 103247 := (sr 1 103247 154871 (by norm_num) (by norm_num) (sr 1 154871 232307 (by norm_num) (by norm_num) (sr 1 232307 348461 (by norm_num) (by norm_num) (sr 3 348461 130673 (by norm_num) (by norm_num) (sr 2 130673 98005 (by norm_num) (by norm_num) (B 98005 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103251 : Reach 103251 := (sr 1 103251 154877 (by norm_num) (by norm_num) (sr 3 154877 58079 (by norm_num) (by norm_num) (B 58079 (by norm_num) (by norm_num) (by norm_num))))
theorem R103255 : Reach 103255 := (sr 1 103255 154883 (by norm_num) (by norm_num) (sr 1 154883 232325 (by norm_num) (by norm_num) (sr 4 232325 43561 (by norm_num) (by norm_num) (B 43561 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103259 : Reach 103259 := (sr 1 103259 154889 (by norm_num) (by norm_num) (sr 2 154889 116167 (by norm_num) (by norm_num) (sr 1 116167 174251 (by norm_num) (by norm_num) (sr 1 174251 261377 (by norm_num) (by norm_num) (sr 2 261377 196033 (by norm_num) (by norm_num) (sr 2 196033 147025 (by norm_num) (by norm_num) (sr 2 147025 110269 (by norm_num) (by norm_num) (sr 3 110269 41351 (by norm_num) (by norm_num) (B 41351 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R103263 : Reach 103263 := (sr 1 103263 154895 (by norm_num) (by norm_num) (sr 1 154895 232343 (by norm_num) (by norm_num) (sr 1 232343 348515 (by norm_num) (by norm_num) (sr 1 348515 522773 (by norm_num) (by norm_num) (sr 6 522773 24505 (by norm_num) (by norm_num) (B 24505 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103267 : Reach 103267 := (sr 1 103267 154901 (by norm_num) (by norm_num) (sr 6 154901 7261 (by norm_num) (by norm_num) (B 7261 (by norm_num) (by norm_num) (by norm_num))))
theorem R103271 : Reach 103271 := (sr 1 103271 154907 (by norm_num) (by norm_num) (sr 1 154907 232361 (by norm_num) (by norm_num) (sr 2 232361 174271 (by norm_num) (by norm_num) (sr 1 174271 261407 (by norm_num) (by norm_num) (sr 1 261407 392111 (by norm_num) (by norm_num) (sr 1 392111 588167 (by norm_num) (by norm_num) (sr 1 588167 882251 (by norm_num) (by norm_num) (sr 1 882251 1323377 (by norm_num) (by norm_num) (sr 2 1323377 992533 (by norm_num) (by norm_num) (sr 6 992533 46525 (by norm_num) (by norm_num) (B 46525 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R103275 : Reach 103275 := (sr 1 103275 154913 (by norm_num) (by norm_num) (sr 2 154913 116185 (by norm_num) (by norm_num) (sr 2 116185 87139 (by norm_num) (by norm_num) (B 87139 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103279 : Reach 103279 := (sr 1 103279 154919 (by norm_num) (by norm_num) (sr 1 154919 232379 (by norm_num) (by norm_num) (sr 1 232379 348569 (by norm_num) (by norm_num) (sr 2 348569 261427 (by norm_num) (by norm_num) (sr 1 261427 392141 (by norm_num) (by norm_num) (sr 3 392141 147053 (by norm_num) (by norm_num) (sr 3 147053 55145 (by norm_num) (by norm_num) (B 55145 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R103283 : Reach 103283 := (sr 1 103283 154925 (by norm_num) (by norm_num) (sr 3 154925 58097 (by norm_num) (by norm_num) (B 58097 (by norm_num) (by norm_num) (by norm_num))))
theorem R103287 : Reach 103287 := (sr 1 103287 154931 (by norm_num) (by norm_num) (sr 1 154931 232397 (by norm_num) (by norm_num) (sr 3 232397 87149 (by norm_num) (by norm_num) (B 87149 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103291 : Reach 103291 := (sr 1 103291 154937 (by norm_num) (by norm_num) (sr 2 154937 116203 (by norm_num) (by norm_num) (sr 1 116203 174305 (by norm_num) (by norm_num) (sr 2 174305 130729 (by norm_num) (by norm_num) (sr 2 130729 98047 (by norm_num) (by norm_num) (B 98047 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103295 : Reach 103295 := (sr 1 103295 154943 (by norm_num) (by norm_num) (sr 1 154943 232415 (by norm_num) (by norm_num) (sr 1 232415 348623 (by norm_num) (by norm_num) (sr 1 348623 522935 (by norm_num) (by norm_num) (sr 1 522935 784403 (by norm_num) (by norm_num) (sr 1 784403 1176605 (by norm_num) (by norm_num) (sr 3 1176605 441227 (by norm_num) (by norm_num) (sr 1 441227 661841 (by norm_num) (by norm_num) (sr 2 661841 496381 (by norm_num) (by norm_num) (sr 3 496381 186143 (by norm_num) (by norm_num) (sr 1 186143 279215 (by norm_num) (by norm_num) (sr 1 279215 418823 (by norm_num) (by norm_num) (sr 1 418823 628235 (by norm_num) (by norm_num) (sr 1 628235 942353 (by norm_num) (by norm_num) (sr 2 942353 706765 (by norm_num) (by norm_num) (sr 3 706765 265037 (by norm_num) (by norm_num) (sr 3 265037 99389 (by norm_num) (by norm_num) (B 99389 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))
theorem R103299 : Reach 103299 := (sr 1 103299 154949 (by norm_num) (by norm_num) (sr 4 154949 29053 (by norm_num) (by norm_num) (B 29053 (by norm_num) (by norm_num) (by norm_num))))
theorem R103303 : Reach 103303 := (sr 1 103303 154955 (by norm_num) (by norm_num) (sr 1 154955 232433 (by norm_num) (by norm_num) (sr 2 232433 174325 (by norm_num) (by norm_num) (sr 5 174325 16343 (by norm_num) (by norm_num) (B 16343 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103307 : Reach 103307 := (sr 1 103307 154961 (by norm_num) (by norm_num) (sr 2 154961 116221 (by norm_num) (by norm_num) (sr 3 116221 43583 (by norm_num) (by norm_num) (B 43583 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103311 : Reach 103311 := (sr 1 103311 154967 (by norm_num) (by norm_num) (sr 1 154967 232451 (by norm_num) (by norm_num) (sr 1 232451 348677 (by norm_num) (by norm_num) (sr 4 348677 65377 (by norm_num) (by norm_num) (B 65377 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103315 : Reach 103315 := (sr 1 103315 154973 (by norm_num) (by norm_num) (sr 3 154973 58115 (by norm_num) (by norm_num) (B 58115 (by norm_num) (by norm_num) (by norm_num))))
theorem R103319 : Reach 103319 := (sr 1 103319 154979 (by norm_num) (by norm_num) (sr 1 154979 232469 (by norm_num) (by norm_num) (sr 6 232469 10897 (by norm_num) (by norm_num) (B 10897 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103323 : Reach 103323 := (sr 1 103323 154985 (by norm_num) (by norm_num) (sr 2 154985 116239 (by norm_num) (by norm_num) (sr 1 116239 174359 (by norm_num) (by norm_num) (sr 1 174359 261539 (by norm_num) (by norm_num) (sr 1 261539 392309 (by norm_num) (by norm_num) (sr 5 392309 36779 (by norm_num) (by norm_num) (B 36779 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R103327 : Reach 103327 := (sr 1 103327 154991 (by norm_num) (by norm_num) (sr 1 154991 232487 (by norm_num) (by norm_num) (sr 1 232487 348731 (by norm_num) (by norm_num) (sr 1 348731 523097 (by norm_num) (by norm_num) (sr 2 523097 392323 (by norm_num) (by norm_num) (sr 1 392323 588485 (by norm_num) (by norm_num) (sr 4 588485 110341 (by norm_num) (by norm_num) (sr 4 110341 20689 (by norm_num) (by norm_num) (B 20689 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R103331 : Reach 103331 := (sr 1 103331 154997 (by norm_num) (by norm_num) (sr 5 154997 14531 (by norm_num) (by norm_num) (B 14531 (by norm_num) (by norm_num) (by norm_num))))
theorem R103335 : Reach 103335 := (sr 1 103335 155003 (by norm_num) (by norm_num) (sr 1 155003 232505 (by norm_num) (by norm_num) (sr 2 232505 174379 (by norm_num) (by norm_num) (sr 1 174379 261569 (by norm_num) (by norm_num) (sr 2 261569 196177 (by norm_num) (by norm_num) (sr 2 196177 147133 (by norm_num) (by norm_num) (sr 3 147133 55175 (by norm_num) (by norm_num) (B 55175 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R103339 : Reach 103339 := (sr 1 103339 155009 (by norm_num) (by norm_num) (sr 2 155009 116257 (by norm_num) (by norm_num) (sr 2 116257 87193 (by norm_num) (by norm_num) (B 87193 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103343 : Reach 103343 := (sr 1 103343 155015 (by norm_num) (by norm_num) (sr 1 155015 232523 (by norm_num) (by norm_num) (sr 1 232523 348785 (by norm_num) (by norm_num) (sr 2 348785 261589 (by norm_num) (by norm_num) (sr 7 261589 6131 (by norm_num) (by norm_num) (B 6131 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103347 : Reach 103347 := (sr 1 103347 155021 (by norm_num) (by norm_num) (sr 3 155021 58133 (by norm_num) (by norm_num) (B 58133 (by norm_num) (by norm_num) (by norm_num))))
theorem R103351 : Reach 103351 := (sr 1 103351 155027 (by norm_num) (by norm_num) (sr 1 155027 232541 (by norm_num) (by norm_num) (sr 3 232541 87203 (by norm_num) (by norm_num) (B 87203 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103355 : Reach 103355 := (sr 1 103355 155033 (by norm_num) (by norm_num) (sr 2 155033 116275 (by norm_num) (by norm_num) (sr 1 116275 174413 (by norm_num) (by norm_num) (sr 3 174413 65405 (by norm_num) (by norm_num) (B 65405 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103359 : Reach 103359 := (sr 1 103359 155039 (by norm_num) (by norm_num) (sr 1 155039 232559 (by norm_num) (by norm_num) (sr 1 232559 348839 (by norm_num) (by norm_num) (sr 1 348839 523259 (by norm_num) (by norm_num) (sr 1 523259 784889 (by norm_num) (by norm_num) (sr 2 784889 588667 (by norm_num) (by norm_num) (sr 1 588667 883001 (by norm_num) (by norm_num) (sr 2 883001 662251 (by norm_num) (by norm_num) (sr 1 662251 993377 (by norm_num) (by norm_num) (sr 2 993377 745033 (by norm_num) (by norm_num) (sr 2 745033 558775 (by norm_num) (by norm_num) (sr 1 558775 838163 (by norm_num) (by norm_num) (sr 1 838163 1257245 (by norm_num) (by norm_num) (sr 3 1257245 471467 (by norm_num) (by norm_num) (sr 1 471467 707201 (by norm_num) (by norm_num) (sr 2 707201 530401 (by norm_num) (by norm_num) (sr 2 530401 397801 (by norm_num) (by norm_num) (sr 2 397801 298351 (by norm_num) (by norm_num) (sr 1 298351 447527 (by norm_num) (by norm_num) (sr 1 447527 671291 (by norm_num) (by norm_num) (sr 1 671291 1006937 (by norm_num) (by norm_num) (sr 2 1006937 755203 (by norm_num) (by norm_num) (sr 1 755203 1132805 (by norm_num) (by norm_num) (sr 4 1132805 212401 (by norm_num) (by norm_num) (sr 2 212401 159301 (by norm_num) (by norm_num) (sr 4 159301 29869 (by norm_num) (by norm_num) (B 29869 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))
theorem R103363 : Reach 103363 := (sr 1 103363 155045 (by norm_num) (by norm_num) (sr 4 155045 29071 (by norm_num) (by norm_num) (B 29071 (by norm_num) (by norm_num) (by norm_num))))
theorem R103367 : Reach 103367 := (sr 1 103367 155051 (by norm_num) (by norm_num) (sr 1 155051 232577 (by norm_num) (by norm_num) (sr 2 232577 174433 (by norm_num) (by norm_num) (sr 2 174433 130825 (by norm_num) (by norm_num) (sr 2 130825 98119 (by norm_num) (by norm_num) (B 98119 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103371 : Reach 103371 := (sr 1 103371 155057 (by norm_num) (by norm_num) (sr 2 155057 116293 (by norm_num) (by norm_num) (sr 4 116293 21805 (by norm_num) (by norm_num) (B 21805 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103375 : Reach 103375 := (sr 1 103375 155063 (by norm_num) (by norm_num) (sr 1 155063 232595 (by norm_num) (by norm_num) (sr 1 232595 348893 (by norm_num) (by norm_num) (sr 3 348893 130835 (by norm_num) (by norm_num) (sr 1 130835 196253 (by norm_num) (by norm_num) (sr 3 196253 73595 (by norm_num) (by norm_num) (B 73595 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R103379 : Reach 103379 := (sr 1 103379 155069 (by norm_num) (by norm_num) (sr 3 155069 58151 (by norm_num) (by norm_num) (B 58151 (by norm_num) (by norm_num) (by norm_num))))
theorem R103383 : Reach 103383 := (sr 1 103383 155075 (by norm_num) (by norm_num) (sr 1 155075 232613 (by norm_num) (by norm_num) (sr 4 232613 43615 (by norm_num) (by norm_num) (B 43615 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103387 : Reach 103387 := (sr 1 103387 155081 (by norm_num) (by norm_num) (sr 2 155081 116311 (by norm_num) (by norm_num) (sr 1 116311 174467 (by norm_num) (by norm_num) (sr 1 174467 261701 (by norm_num) (by norm_num) (sr 4 261701 49069 (by norm_num) (by norm_num) (B 49069 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103391 : Reach 103391 := (sr 1 103391 155087 (by norm_num) (by norm_num) (sr 1 155087 232631 (by norm_num) (by norm_num) (sr 1 232631 348947 (by norm_num) (by norm_num) (sr 1 348947 523421 (by norm_num) (by norm_num) (sr 3 523421 196283 (by norm_num) (by norm_num) (sr 1 196283 294425 (by norm_num) (by norm_num) (sr 2 294425 220819 (by norm_num) (by norm_num) (sr 1 220819 331229 (by norm_num) (by norm_num) (sr 3 331229 124211 (by norm_num) (by norm_num) (sr 1 124211 186317 (by norm_num) (by norm_num) (sr 3 186317 69869 (by norm_num) (by norm_num) (B 69869 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R103395 : Reach 103395 := (sr 1 103395 155093 (by norm_num) (by norm_num) (sr 7 155093 3635 (by norm_num) (by norm_num) (B 3635 (by norm_num) (by norm_num) (by norm_num))))
theorem R103399 : Reach 103399 := (sr 1 103399 155099 (by norm_num) (by norm_num) (sr 1 155099 232649 (by norm_num) (by norm_num) (sr 2 232649 174487 (by norm_num) (by norm_num) (sr 1 174487 261731 (by norm_num) (by norm_num) (sr 1 261731 392597 (by norm_num) (by norm_num) (sr 6 392597 18403 (by norm_num) (by norm_num) (B 18403 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R103403 : Reach 103403 := (sr 1 103403 155105 (by norm_num) (by norm_num) (sr 2 155105 116329 (by norm_num) (by norm_num) (sr 2 116329 87247 (by norm_num) (by norm_num) (B 87247 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103407 : Reach 103407 := (sr 1 103407 155111 (by norm_num) (by norm_num) (sr 1 155111 232667 (by norm_num) (by norm_num) (sr 1 232667 349001 (by norm_num) (by norm_num) (sr 2 349001 261751 (by norm_num) (by norm_num) (sr 1 261751 392627 (by norm_num) (by norm_num) (sr 1 392627 588941 (by norm_num) (by norm_num) (sr 3 588941 220853 (by norm_num) (by norm_num) (sr 5 220853 20705 (by norm_num) (by norm_num) (B 20705 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R103411 : Reach 103411 := (sr 1 103411 155117 (by norm_num) (by norm_num) (sr 3 155117 58169 (by norm_num) (by norm_num) (B 58169 (by norm_num) (by norm_num) (by norm_num))))
theorem R103415 : Reach 103415 := (sr 1 103415 155123 (by norm_num) (by norm_num) (sr 1 155123 232685 (by norm_num) (by norm_num) (sr 3 232685 87257 (by norm_num) (by norm_num) (B 87257 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103419 : Reach 103419 := (sr 1 103419 155129 (by norm_num) (by norm_num) (sr 2 155129 116347 (by norm_num) (by norm_num) (sr 1 116347 174521 (by norm_num) (by norm_num) (sr 2 174521 130891 (by norm_num) (by norm_num) (sr 1 130891 196337 (by norm_num) (by norm_num) (sr 2 196337 147253 (by norm_num) (by norm_num) (sr 5 147253 13805 (by norm_num) (by norm_num) (B 13805 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R103423 : Reach 103423 := (sr 1 103423 155135 (by norm_num) (by norm_num) (sr 1 155135 232703 (by norm_num) (by norm_num) (sr 1 232703 349055 (by norm_num) (by norm_num) (sr 1 349055 523583 (by norm_num) (by norm_num) (sr 1 523583 785375 (by norm_num) (by norm_num) (sr 1 785375 1178063 (by norm_num) (by norm_num) (sr 1 1178063 1767095 (by norm_num) (by norm_num) (sr 1 1767095 2650643 (by norm_num) (by norm_num) (sr 1 2650643 3975965 (by norm_num) (by norm_num) (sr 3 3975965 1490987 (by norm_num) (by norm_num) (sr 1 1490987 2236481 (by norm_num) (by norm_num) (sr 2 2236481 1677361 (by norm_num) (by norm_num) (sr 2 1677361 1258021 (by norm_num) (by norm_num) (sr 4 1258021 235879 (by norm_num) (by norm_num) (sr 1 235879 353819 (by norm_num) (by norm_num) (sr 1 353819 530729 (by norm_num) (by norm_num) (sr 2 530729 398047 (by norm_num) (by norm_num) (sr 1 398047 597071 (by norm_num) (by norm_num) (sr 1 597071 895607 (by norm_num) (by norm_num) (sr 1 895607 1343411 (by norm_num) (by norm_num) (sr 1 1343411 2015117 (by norm_num) (by norm_num) (sr 3 2015117 755669 (by norm_num) (by norm_num) (sr 7 755669 17711 (by norm_num) (by norm_num) (B 17711 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))
theorem R103427 : Reach 103427 := (sr 1 103427 155141 (by norm_num) (by norm_num) (sr 4 155141 29089 (by norm_num) (by norm_num) (B 29089 (by norm_num) (by norm_num) (by norm_num))))
theorem R103431 : Reach 103431 := (sr 1 103431 155147 (by norm_num) (by norm_num) (sr 1 155147 232721 (by norm_num) (by norm_num) (sr 2 232721 174541 (by norm_num) (by norm_num) (sr 3 174541 65453 (by norm_num) (by norm_num) (B 65453 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103435 : Reach 103435 := (sr 1 103435 155153 (by norm_num) (by norm_num) (sr 2 155153 116365 (by norm_num) (by norm_num) (sr 3 116365 43637 (by norm_num) (by norm_num) (B 43637 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103439 : Reach 103439 := (sr 1 103439 155159 (by norm_num) (by norm_num) (sr 1 155159 232739 (by norm_num) (by norm_num) (sr 1 232739 349109 (by norm_num) (by norm_num) (sr 5 349109 32729 (by norm_num) (by norm_num) (B 32729 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103443 : Reach 103443 := (sr 1 103443 155165 (by norm_num) (by norm_num) (sr 3 155165 58187 (by norm_num) (by norm_num) (B 58187 (by norm_num) (by norm_num) (by norm_num))))
theorem R103447 : Reach 103447 := (sr 1 103447 155171 (by norm_num) (by norm_num) (sr 1 155171 232757 (by norm_num) (by norm_num) (sr 5 232757 21821 (by norm_num) (by norm_num) (B 21821 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103451 : Reach 103451 := (sr 1 103451 155177 (by norm_num) (by norm_num) (sr 2 155177 116383 (by norm_num) (by norm_num) (sr 1 116383 174575 (by norm_num) (by norm_num) (sr 1 174575 261863 (by norm_num) (by norm_num) (sr 1 261863 392795 (by norm_num) (by norm_num) (sr 1 392795 589193 (by norm_num) (by norm_num) (sr 2 589193 441895 (by norm_num) (by norm_num) (sr 1 441895 662843 (by norm_num) (by norm_num) (sr 1 662843 994265 (by norm_num) (by norm_num) (sr 2 994265 745699 (by norm_num) (by norm_num) (sr 1 745699 1118549 (by norm_num) (by norm_num) (sr 10 1118549 3277 (by norm_num) (by norm_num) (B 3277 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R103455 : Reach 103455 := (sr 1 103455 155183 (by norm_num) (by norm_num) (sr 1 155183 232775 (by norm_num) (by norm_num) (sr 1 232775 349163 (by norm_num) (by norm_num) (sr 1 349163 523745 (by norm_num) (by norm_num) (sr 2 523745 392809 (by norm_num) (by norm_num) (sr 2 392809 294607 (by norm_num) (by norm_num) (sr 1 294607 441911 (by norm_num) (by norm_num) (sr 1 441911 662867 (by norm_num) (by norm_num) (sr 1 662867 994301 (by norm_num) (by norm_num) (sr 3 994301 372863 (by norm_num) (by norm_num) (sr 1 372863 559295 (by norm_num) (by norm_num) (sr 1 559295 838943 (by norm_num) (by norm_num) (sr 1 838943 1258415 (by norm_num) (by norm_num) (sr 1 1258415 1887623 (by norm_num) (by norm_num) (sr 1 1887623 2831435 (by norm_num) (by norm_num) (sr 1 2831435 4247153 (by norm_num) (by norm_num) (sr 2 4247153 3185365 (by norm_num) (by norm_num) (sr 7 3185365 74657 (by norm_num) (by norm_num) (B 74657 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))
theorem R103459 : Reach 103459 := (sr 1 103459 155189 (by norm_num) (by norm_num) (sr 5 155189 14549 (by norm_num) (by norm_num) (B 14549 (by norm_num) (by norm_num) (by norm_num))))
theorem R103463 : Reach 103463 := (sr 1 103463 155195 (by norm_num) (by norm_num) (sr 1 155195 232793 (by norm_num) (by norm_num) (sr 2 232793 174595 (by norm_num) (by norm_num) (sr 1 174595 261893 (by norm_num) (by norm_num) (sr 4 261893 49105 (by norm_num) (by norm_num) (B 49105 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103467 : Reach 103467 := (sr 1 103467 155201 (by norm_num) (by norm_num) (sr 2 155201 116401 (by norm_num) (by norm_num) (sr 2 116401 87301 (by norm_num) (by norm_num) (B 87301 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103471 : Reach 103471 := (sr 1 103471 155207 (by norm_num) (by norm_num) (sr 1 155207 232811 (by norm_num) (by norm_num) (sr 1 232811 349217 (by norm_num) (by norm_num) (sr 2 349217 261913 (by norm_num) (by norm_num) (sr 2 261913 196435 (by norm_num) (by norm_num) (sr 1 196435 294653 (by norm_num) (by norm_num) (sr 3 294653 110495 (by norm_num) (by norm_num) (sr 1 110495 165743 (by norm_num) (by norm_num) (sr 1 165743 248615 (by norm_num) (by norm_num) (sr 1 248615 372923 (by norm_num) (by norm_num) (sr 1 372923 559385 (by norm_num) (by norm_num) (sr 2 559385 419539 (by norm_num) (by norm_num) (sr 1 419539 629309 (by norm_num) (by norm_num) (sr 3 629309 235991 (by norm_num) (by norm_num) (sr 1 235991 353987 (by norm_num) (by norm_num) (sr 1 353987 530981 (by norm_num) (by norm_num) (sr 4 530981 99559 (by norm_num) (by norm_num) (B 99559 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))
theorem R103475 : Reach 103475 := (sr 1 103475 155213 (by norm_num) (by norm_num) (sr 3 155213 58205 (by norm_num) (by norm_num) (B 58205 (by norm_num) (by norm_num) (by norm_num))))
theorem R103479 : Reach 103479 := (sr 1 103479 155219 (by norm_num) (by norm_num) (sr 1 155219 232829 (by norm_num) (by norm_num) (sr 3 232829 87311 (by norm_num) (by norm_num) (B 87311 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103483 : Reach 103483 := (sr 1 103483 155225 (by norm_num) (by norm_num) (sr 2 155225 116419 (by norm_num) (by norm_num) (sr 1 116419 174629 (by norm_num) (by norm_num) (sr 4 174629 32743 (by norm_num) (by norm_num) (B 32743 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103487 : Reach 103487 := (sr 1 103487 155231 (by norm_num) (by norm_num) (sr 1 155231 232847 (by norm_num) (by norm_num) (sr 1 232847 349271 (by norm_num) (by norm_num) (sr 1 349271 523907 (by norm_num) (by norm_num) (sr 1 523907 785861 (by norm_num) (by norm_num) (sr 4 785861 147349 (by norm_num) (by norm_num) (sr 6 147349 6907 (by norm_num) (by norm_num) (B 6907 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R103491 : Reach 103491 := (sr 1 103491 155237 (by norm_num) (by norm_num) (sr 4 155237 29107 (by norm_num) (by norm_num) (B 29107 (by norm_num) (by norm_num) (by norm_num))))
theorem R103495 : Reach 103495 := (sr 1 103495 155243 (by norm_num) (by norm_num) (sr 1 155243 232865 (by norm_num) (by norm_num) (sr 2 232865 174649 (by norm_num) (by norm_num) (sr 2 174649 130987 (by norm_num) (by norm_num) (sr 1 130987 196481 (by norm_num) (by norm_num) (sr 2 196481 147361 (by norm_num) (by norm_num) (sr 2 147361 110521 (by norm_num) (by norm_num) (sr 2 110521 82891 (by norm_num) (by norm_num) (B 82891 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R103499 : Reach 103499 := (sr 1 103499 155249 (by norm_num) (by norm_num) (sr 2 155249 116437 (by norm_num) (by norm_num) (sr 7 116437 2729 (by norm_num) (by norm_num) (B 2729 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103503 : Reach 103503 := (sr 1 103503 155255 (by norm_num) (by norm_num) (sr 1 155255 232883 (by norm_num) (by norm_num) (sr 1 232883 349325 (by norm_num) (by norm_num) (sr 3 349325 130997 (by norm_num) (by norm_num) (sr 5 130997 12281 (by norm_num) (by norm_num) (B 12281 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103507 : Reach 103507 := (sr 1 103507 155261 (by norm_num) (by norm_num) (sr 3 155261 58223 (by norm_num) (by norm_num) (B 58223 (by norm_num) (by norm_num) (by norm_num))))
theorem R103511 : Reach 103511 := (sr 1 103511 155267 (by norm_num) (by norm_num) (sr 1 155267 232901 (by norm_num) (by norm_num) (sr 4 232901 43669 (by norm_num) (by norm_num) (B 43669 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103515 : Reach 103515 := (sr 1 103515 155273 (by norm_num) (by norm_num) (sr 2 155273 116455 (by norm_num) (by norm_num) (sr 1 116455 174683 (by norm_num) (by norm_num) (sr 1 174683 262025 (by norm_num) (by norm_num) (sr 2 262025 196519 (by norm_num) (by norm_num) (sr 1 196519 294779 (by norm_num) (by norm_num) (sr 1 294779 442169 (by norm_num) (by norm_num) (sr 2 442169 331627 (by norm_num) (by norm_num) (sr 1 331627 497441 (by norm_num) (by norm_num) (sr 2 497441 373081 (by norm_num) (by norm_num) (sr 2 373081 279811 (by norm_num) (by norm_num) (sr 1 279811 419717 (by norm_num) (by norm_num) (sr 4 419717 78697 (by norm_num) (by norm_num) (B 78697 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R103519 : Reach 103519 := (sr 1 103519 155279 (by norm_num) (by norm_num) (sr 1 155279 232919 (by norm_num) (by norm_num) (sr 1 232919 349379 (by norm_num) (by norm_num) (sr 1 349379 524069 (by norm_num) (by norm_num) (sr 4 524069 98263 (by norm_num) (by norm_num) (B 98263 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103523 : Reach 103523 := (sr 1 103523 155285 (by norm_num) (by norm_num) (sr 6 155285 7279 (by norm_num) (by norm_num) (B 7279 (by norm_num) (by norm_num) (by norm_num))))
theorem R103527 : Reach 103527 := (sr 1 103527 155291 (by norm_num) (by norm_num) (sr 1 155291 232937 (by norm_num) (by norm_num) (sr 2 232937 174703 (by norm_num) (by norm_num) (sr 1 174703 262055 (by norm_num) (by norm_num) (sr 1 262055 393083 (by norm_num) (by norm_num) (sr 1 393083 589625 (by norm_num) (by norm_num) (sr 2 589625 442219 (by norm_num) (by norm_num) (sr 1 442219 663329 (by norm_num) (by norm_num) (sr 2 663329 497497 (by norm_num) (by norm_num) (sr 2 497497 373123 (by norm_num) (by norm_num) (sr 1 373123 559685 (by norm_num) (by norm_num) (sr 4 559685 104941 (by norm_num) (by norm_num) (sr 3 104941 39353 (by norm_num) (by norm_num) (B 39353 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R103531 : Reach 103531 := (sr 1 103531 155297 (by norm_num) (by norm_num) (sr 2 155297 116473 (by norm_num) (by norm_num) (sr 2 116473 87355 (by norm_num) (by norm_num) (B 87355 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103535 : Reach 103535 := (sr 1 103535 155303 (by norm_num) (by norm_num) (sr 1 155303 232955 (by norm_num) (by norm_num) (sr 1 232955 349433 (by norm_num) (by norm_num) (sr 2 349433 262075 (by norm_num) (by norm_num) (sr 1 262075 393113 (by norm_num) (by norm_num) (sr 2 393113 294835 (by norm_num) (by norm_num) (sr 1 294835 442253 (by norm_num) (by norm_num) (sr 3 442253 165845 (by norm_num) (by norm_num) (sr 7 165845 3887 (by norm_num) (by norm_num) (B 3887 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R103539 : Reach 103539 := (sr 1 103539 155309 (by norm_num) (by norm_num) (sr 3 155309 58241 (by norm_num) (by norm_num) (B 58241 (by norm_num) (by norm_num) (by norm_num))))
theorem R103543 : Reach 103543 := (sr 1 103543 155315 (by norm_num) (by norm_num) (sr 1 155315 232973 (by norm_num) (by norm_num) (sr 3 232973 87365 (by norm_num) (by norm_num) (B 87365 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103547 : Reach 103547 := (sr 1 103547 155321 (by norm_num) (by norm_num) (sr 2 155321 116491 (by norm_num) (by norm_num) (sr 1 116491 174737 (by norm_num) (by norm_num) (sr 2 174737 131053 (by norm_num) (by norm_num) (sr 3 131053 49145 (by norm_num) (by norm_num) (B 49145 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103551 : Reach 103551 := (sr 1 103551 155327 (by norm_num) (by norm_num) (sr 1 155327 232991 (by norm_num) (by norm_num) (sr 1 232991 349487 (by norm_num) (by norm_num) (sr 1 349487 524231 (by norm_num) (by norm_num) (sr 1 524231 786347 (by norm_num) (by norm_num) (sr 1 786347 1179521 (by norm_num) (by norm_num) (sr 2 1179521 884641 (by norm_num) (by norm_num) (sr 2 884641 663481 (by norm_num) (by norm_num) (sr 2 663481 497611 (by norm_num) (by norm_num) (sr 1 497611 746417 (by norm_num) (by norm_num) (sr 2 746417 559813 (by norm_num) (by norm_num) (sr 4 559813 104965 (by norm_num) (by norm_num) (sr 4 104965 19681 (by norm_num) (by norm_num) (B 19681 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R103555 : Reach 103555 := (sr 1 103555 155333 (by norm_num) (by norm_num) (sr 4 155333 29125 (by norm_num) (by norm_num) (B 29125 (by norm_num) (by norm_num) (by norm_num))))
theorem R103559 : Reach 103559 := (sr 1 103559 155339 (by norm_num) (by norm_num) (sr 1 155339 233009 (by norm_num) (by norm_num) (sr 2 233009 174757 (by norm_num) (by norm_num) (sr 4 174757 32767 (by norm_num) (by norm_num) (B 32767 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103563 : Reach 103563 := (sr 1 103563 155345 (by norm_num) (by norm_num) (sr 2 155345 116509 (by norm_num) (by norm_num) (sr 3 116509 43691 (by norm_num) (by norm_num) (B 43691 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103567 : Reach 103567 := (sr 1 103567 155351 (by norm_num) (by norm_num) (sr 1 155351 233027 (by norm_num) (by norm_num) (sr 1 233027 349541 (by norm_num) (by norm_num) (sr 4 349541 65539 (by norm_num) (by norm_num) (B 65539 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103571 : Reach 103571 := (sr 1 103571 155357 (by norm_num) (by norm_num) (sr 3 155357 58259 (by norm_num) (by norm_num) (B 58259 (by norm_num) (by norm_num) (by norm_num))))
theorem R103575 : Reach 103575 := (sr 1 103575 155363 (by norm_num) (by norm_num) (sr 1 155363 233045 (by norm_num) (by norm_num) (sr 8 233045 2731 (by norm_num) (by norm_num) (B 2731 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103579 : Reach 103579 := (sr 1 103579 155369 (by norm_num) (by norm_num) (sr 2 155369 116527 (by norm_num) (by norm_num) (sr 1 116527 174791 (by norm_num) (by norm_num) (sr 1 174791 262187 (by norm_num) (by norm_num) (sr 1 262187 393281 (by norm_num) (by norm_num) (sr 2 393281 294961 (by norm_num) (by norm_num) (sr 2 294961 221221 (by norm_num) (by norm_num) (sr 4 221221 41479 (by norm_num) (by norm_num) (B 41479 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R103583 : Reach 103583 := (sr 1 103583 155375 (by norm_num) (by norm_num) (sr 1 155375 233063 (by norm_num) (by norm_num) (sr 1 233063 349595 (by norm_num) (by norm_num) (sr 1 349595 524393 (by norm_num) (by norm_num) (sr 2 524393 393295 (by norm_num) (by norm_num) (sr 1 393295 589943 (by norm_num) (by norm_num) (sr 1 589943 884915 (by norm_num) (by norm_num) (sr 1 884915 1327373 (by norm_num) (by norm_num) (sr 3 1327373 497765 (by norm_num) (by norm_num) (sr 4 497765 93331 (by norm_num) (by norm_num) (B 93331 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R103587 : Reach 103587 := (sr 1 103587 155381 (by norm_num) (by norm_num) (sr 5 155381 14567 (by norm_num) (by norm_num) (B 14567 (by norm_num) (by norm_num) (by norm_num))))
theorem R103591 : Reach 103591 := (sr 1 103591 155387 (by norm_num) (by norm_num) (sr 1 155387 233081 (by norm_num) (by norm_num) (sr 2 233081 174811 (by norm_num) (by norm_num) (sr 1 174811 262217 (by norm_num) (by norm_num) (sr 2 262217 196663 (by norm_num) (by norm_num) (sr 1 196663 294995 (by norm_num) (by norm_num) (sr 1 294995 442493 (by norm_num) (by norm_num) (sr 3 442493 165935 (by norm_num) (by norm_num) (sr 1 165935 248903 (by norm_num) (by norm_num) (sr 1 248903 373355 (by norm_num) (by norm_num) (sr 1 373355 560033 (by norm_num) (by norm_num) (sr 2 560033 420025 (by norm_num) (by norm_num) (sr 2 420025 315019 (by norm_num) (by norm_num) (sr 1 315019 472529 (by norm_num) (by norm_num) (sr 2 472529 354397 (by norm_num) (by norm_num) (sr 3 354397 132899 (by norm_num) (by norm_num) (sr 1 132899 199349 (by norm_num) (by norm_num) (sr 5 199349 18689 (by norm_num) (by norm_num) (B 18689 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))
theorem R103595 : Reach 103595 := (sr 1 103595 155393 (by norm_num) (by norm_num) (sr 2 155393 116545 (by norm_num) (by norm_num) (sr 2 116545 87409 (by norm_num) (by norm_num) (B 87409 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103599 : Reach 103599 := (sr 1 103599 155399 (by norm_num) (by norm_num) (sr 1 155399 233099 (by norm_num) (by norm_num) (sr 1 233099 349649 (by norm_num) (by norm_num) (sr 2 349649 262237 (by norm_num) (by norm_num) (sr 3 262237 98339 (by norm_num) (by norm_num) (B 98339 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103603 : Reach 103603 := (sr 1 103603 155405 (by norm_num) (by norm_num) (sr 3 155405 58277 (by norm_num) (by norm_num) (B 58277 (by norm_num) (by norm_num) (by norm_num))))
theorem R103607 : Reach 103607 := (sr 1 103607 155411 (by norm_num) (by norm_num) (sr 1 155411 233117 (by norm_num) (by norm_num) (sr 3 233117 87419 (by norm_num) (by norm_num) (B 87419 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103611 : Reach 103611 := (sr 1 103611 155417 (by norm_num) (by norm_num) (sr 2 155417 116563 (by norm_num) (by norm_num) (sr 1 116563 174845 (by norm_num) (by norm_num) (sr 3 174845 65567 (by norm_num) (by norm_num) (B 65567 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103615 : Reach 103615 := (sr 1 103615 155423 (by norm_num) (by norm_num) (sr 1 155423 233135 (by norm_num) (by norm_num) (sr 1 233135 349703 (by norm_num) (by norm_num) (sr 1 349703 524555 (by norm_num) (by norm_num) (sr 1 524555 786833 (by norm_num) (by norm_num) (sr 2 786833 590125 (by norm_num) (by norm_num) (sr 3 590125 221297 (by norm_num) (by norm_num) (sr 2 221297 165973 (by norm_num) (by norm_num) (sr 8 165973 1945 (by norm_num) (by norm_num) (B 1945 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R103619 : Reach 103619 := (sr 1 103619 155429 (by norm_num) (by norm_num) (sr 4 155429 29143 (by norm_num) (by norm_num) (B 29143 (by norm_num) (by norm_num) (by norm_num))))
theorem R103623 : Reach 103623 := (sr 1 103623 155435 (by norm_num) (by norm_num) (sr 1 155435 233153 (by norm_num) (by norm_num) (sr 2 233153 174865 (by norm_num) (by norm_num) (sr 2 174865 131149 (by norm_num) (by norm_num) (sr 3 131149 49181 (by norm_num) (by norm_num) (B 49181 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103627 : Reach 103627 := (sr 1 103627 155441 (by norm_num) (by norm_num) (sr 2 155441 116581 (by norm_num) (by norm_num) (sr 4 116581 21859 (by norm_num) (by norm_num) (B 21859 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103631 : Reach 103631 := (sr 1 103631 155447 (by norm_num) (by norm_num) (sr 1 155447 233171 (by norm_num) (by norm_num) (sr 1 233171 349757 (by norm_num) (by norm_num) (sr 3 349757 131159 (by norm_num) (by norm_num) (sr 1 131159 196739 (by norm_num) (by norm_num) (sr 1 196739 295109 (by norm_num) (by norm_num) (sr 4 295109 55333 (by norm_num) (by norm_num) (B 55333 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R103635 : Reach 103635 := (sr 1 103635 155453 (by norm_num) (by norm_num) (sr 3 155453 58295 (by norm_num) (by norm_num) (B 58295 (by norm_num) (by norm_num) (by norm_num))))
theorem R103639 : Reach 103639 := (sr 1 103639 155459 (by norm_num) (by norm_num) (sr 1 155459 233189 (by norm_num) (by norm_num) (sr 4 233189 43723 (by norm_num) (by norm_num) (B 43723 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103643 : Reach 103643 := (sr 1 103643 155465 (by norm_num) (by norm_num) (sr 2 155465 116599 (by norm_num) (by norm_num) (sr 1 116599 174899 (by norm_num) (by norm_num) (sr 1 174899 262349 (by norm_num) (by norm_num) (sr 3 262349 98381 (by norm_num) (by norm_num) (B 98381 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103647 : Reach 103647 := (sr 1 103647 155471 (by norm_num) (by norm_num) (sr 1 155471 233207 (by norm_num) (by norm_num) (sr 1 233207 349811 (by norm_num) (by norm_num) (sr 1 349811 524717 (by norm_num) (by norm_num) (sr 3 524717 196769 (by norm_num) (by norm_num) (sr 2 196769 147577 (by norm_num) (by norm_num) (sr 2 147577 110683 (by norm_num) (by norm_num) (sr 1 110683 166025 (by norm_num) (by norm_num) (sr 2 166025 124519 (by norm_num) (by norm_num) (sr 1 124519 186779 (by norm_num) (by norm_num) (sr 1 186779 280169 (by norm_num) (by norm_num) (sr 2 280169 210127 (by norm_num) (by norm_num) (sr 1 210127 315191 (by norm_num) (by norm_num) (sr 1 315191 472787 (by norm_num) (by norm_num) (sr 1 472787 709181 (by norm_num) (by norm_num) (sr 3 709181 265943 (by norm_num) (by norm_num) (sr 1 265943 398915 (by norm_num) (by norm_num) (sr 1 398915 598373 (by norm_num) (by norm_num) (sr 4 598373 112195 (by norm_num) (by norm_num) (sr 1 112195 168293 (by norm_num) (by norm_num) (sr 4 168293 31555 (by norm_num) (by norm_num) (B 31555 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))
theorem R103651 : Reach 103651 := (sr 1 103651 155477 (by norm_num) (by norm_num) (sr 9 155477 911 (by norm_num) (by norm_num) (B 911 (by norm_num) (by norm_num) (by norm_num))))
theorem R103655 : Reach 103655 := (sr 1 103655 155483 (by norm_num) (by norm_num) (sr 1 155483 233225 (by norm_num) (by norm_num) (sr 2 233225 174919 (by norm_num) (by norm_num) (sr 1 174919 262379 (by norm_num) (by norm_num) (sr 1 262379 393569 (by norm_num) (by norm_num) (sr 2 393569 295177 (by norm_num) (by norm_num) (sr 2 295177 221383 (by norm_num) (by norm_num) (sr 1 221383 332075 (by norm_num) (by norm_num) (sr 1 332075 498113 (by norm_num) (by norm_num) (sr 2 498113 373585 (by norm_num) (by norm_num) (sr 2 373585 280189 (by norm_num) (by norm_num) (sr 3 280189 105071 (by norm_num) (by norm_num) (sr 1 105071 157607 (by norm_num) (by norm_num) (sr 1 157607 236411 (by norm_num) (by norm_num) (sr 1 236411 354617 (by norm_num) (by norm_num) (sr 2 354617 265963 (by norm_num) (by norm_num) (sr 1 265963 398945 (by norm_num) (by norm_num) (sr 2 398945 299209 (by norm_num) (by norm_num) (sr 2 299209 224407 (by norm_num) (by norm_num) (sr 1 224407 336611 (by norm_num) (by norm_num) (sr 1 336611 504917 (by norm_num) (by norm_num) (sr 8 504917 5917 (by norm_num) (by norm_num) (B 5917 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R103659 : Reach 103659 := (sr 1 103659 155489 (by norm_num) (by norm_num) (sr 2 155489 116617 (by norm_num) (by norm_num) (sr 2 116617 87463 (by norm_num) (by norm_num) (B 87463 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103663 : Reach 103663 := (sr 1 103663 155495 (by norm_num) (by norm_num) (sr 1 155495 233243 (by norm_num) (by norm_num) (sr 1 233243 349865 (by norm_num) (by norm_num) (sr 2 349865 262399 (by norm_num) (by norm_num) (sr 1 262399 393599 (by norm_num) (by norm_num) (sr 1 393599 590399 (by norm_num) (by norm_num) (sr 1 590399 885599 (by norm_num) (by norm_num) (sr 1 885599 1328399 (by norm_num) (by norm_num) (sr 1 1328399 1992599 (by norm_num) (by norm_num) (sr 1 1992599 2988899 (by norm_num) (by norm_num) (sr 1 2988899 4483349 (by norm_num) (by norm_num) (sr 6 4483349 210157 (by norm_num) (by norm_num) (sr 3 210157 78809 (by norm_num) (by norm_num) (B 78809 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R103667 : Reach 103667 := (sr 1 103667 155501 (by norm_num) (by norm_num) (sr 3 155501 58313 (by norm_num) (by norm_num) (B 58313 (by norm_num) (by norm_num) (by norm_num))))
theorem R103671 : Reach 103671 := (sr 1 103671 155507 (by norm_num) (by norm_num) (sr 1 155507 233261 (by norm_num) (by norm_num) (sr 3 233261 87473 (by norm_num) (by norm_num) (B 87473 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103675 : Reach 103675 := (sr 1 103675 155513 (by norm_num) (by norm_num) (sr 2 155513 116635 (by norm_num) (by norm_num) (sr 1 116635 174953 (by norm_num) (by norm_num) (sr 2 174953 131215 (by norm_num) (by norm_num) (sr 1 131215 196823 (by norm_num) (by norm_num) (sr 1 196823 295235 (by norm_num) (by norm_num) (sr 1 295235 442853 (by norm_num) (by norm_num) (sr 4 442853 83035 (by norm_num) (by norm_num) (B 83035 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R103679 : Reach 103679 := (sr 1 103679 155519 (by norm_num) (by norm_num) (sr 1 155519 233279 (by norm_num) (by norm_num) (sr 1 233279 349919 (by norm_num) (by norm_num) (sr 1 349919 524879 (by norm_num) (by norm_num) (sr 1 524879 787319 (by norm_num) (by norm_num) (sr 1 787319 1180979 (by norm_num) (by norm_num) (sr 1 1180979 1771469 (by norm_num) (by norm_num) (sr 3 1771469 664301 (by norm_num) (by norm_num) (sr 3 664301 249113 (by norm_num) (by norm_num) (sr 2 249113 186835 (by norm_num) (by norm_num) (sr 1 186835 280253 (by norm_num) (by norm_num) (sr 3 280253 105095 (by norm_num) (by norm_num) (sr 1 105095 157643 (by norm_num) (by norm_num) (sr 1 157643 236465 (by norm_num) (by norm_num) (sr 2 236465 177349 (by norm_num) (by norm_num) (sr 4 177349 33253 (by norm_num) (by norm_num) (B 33253 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))
theorem R103683 : Reach 103683 := (sr 1 103683 155525 (by norm_num) (by norm_num) (sr 4 155525 29161 (by norm_num) (by norm_num) (B 29161 (by norm_num) (by norm_num) (by norm_num))))
theorem R103687 : Reach 103687 := (sr 1 103687 155531 (by norm_num) (by norm_num) (sr 1 155531 233297 (by norm_num) (by norm_num) (sr 2 233297 174973 (by norm_num) (by norm_num) (sr 3 174973 65615 (by norm_num) (by norm_num) (B 65615 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103691 : Reach 103691 := (sr 1 103691 155537 (by norm_num) (by norm_num) (sr 2 155537 116653 (by norm_num) (by norm_num) (sr 3 116653 43745 (by norm_num) (by norm_num) (B 43745 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103695 : Reach 103695 := (sr 1 103695 155543 (by norm_num) (by norm_num) (sr 1 155543 233315 (by norm_num) (by norm_num) (sr 1 233315 349973 (by norm_num) (by norm_num) (sr 6 349973 16405 (by norm_num) (by norm_num) (B 16405 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103699 : Reach 103699 := (sr 1 103699 155549 (by norm_num) (by norm_num) (sr 3 155549 58331 (by norm_num) (by norm_num) (B 58331 (by norm_num) (by norm_num) (by norm_num))))
theorem R103703 : Reach 103703 := (sr 1 103703 155555 (by norm_num) (by norm_num) (sr 1 155555 233333 (by norm_num) (by norm_num) (sr 5 233333 21875 (by norm_num) (by norm_num) (B 21875 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103707 : Reach 103707 := (sr 1 103707 155561 (by norm_num) (by norm_num) (sr 2 155561 116671 (by norm_num) (by norm_num) (sr 1 116671 175007 (by norm_num) (by norm_num) (sr 1 175007 262511 (by norm_num) (by norm_num) (sr 1 262511 393767 (by norm_num) (by norm_num) (sr 1 393767 590651 (by norm_num) (by norm_num) (sr 1 590651 885977 (by norm_num) (by norm_num) (sr 2 885977 664483 (by norm_num) (by norm_num) (sr 1 664483 996725 (by norm_num) (by norm_num) (sr 5 996725 93443 (by norm_num) (by norm_num) (B 93443 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R103711 : Reach 103711 := (sr 1 103711 155567 (by norm_num) (by norm_num) (sr 1 155567 233351 (by norm_num) (by norm_num) (sr 1 233351 350027 (by norm_num) (by norm_num) (sr 1 350027 525041 (by norm_num) (by norm_num) (sr 2 525041 393781 (by norm_num) (by norm_num) (sr 5 393781 36917 (by norm_num) (by norm_num) (B 36917 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R103715 : Reach 103715 := (sr 1 103715 155573 (by norm_num) (by norm_num) (sr 5 155573 14585 (by norm_num) (by norm_num) (B 14585 (by norm_num) (by norm_num) (by norm_num))))
theorem R103719 : Reach 103719 := (sr 1 103719 155579 (by norm_num) (by norm_num) (sr 1 155579 233369 (by norm_num) (by norm_num) (sr 2 233369 175027 (by norm_num) (by norm_num) (sr 1 175027 262541 (by norm_num) (by norm_num) (sr 3 262541 98453 (by norm_num) (by norm_num) (B 98453 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103723 : Reach 103723 := (sr 1 103723 155585 (by norm_num) (by norm_num) (sr 2 155585 116689 (by norm_num) (by norm_num) (sr 2 116689 87517 (by norm_num) (by norm_num) (B 87517 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103727 : Reach 103727 := (sr 1 103727 155591 (by norm_num) (by norm_num) (sr 1 155591 233387 (by norm_num) (by norm_num) (sr 1 233387 350081 (by norm_num) (by norm_num) (sr 2 350081 262561 (by norm_num) (by norm_num) (sr 2 262561 196921 (by norm_num) (by norm_num) (sr 2 196921 147691 (by norm_num) (by norm_num) (sr 1 147691 221537 (by norm_num) (by norm_num) (sr 2 221537 166153 (by norm_num) (by norm_num) (sr 2 166153 124615 (by norm_num) (by norm_num) (sr 1 124615 186923 (by norm_num) (by norm_num) (sr 1 186923 280385 (by norm_num) (by norm_num) (sr 2 280385 210289 (by norm_num) (by norm_num) (sr 2 210289 157717 (by norm_num) (by norm_num) (sr 6 157717 7393 (by norm_num) (by norm_num) (B 7393 (by norm_num) (by norm_num) (by norm_num))))))))))))))))
theorem R103731 : Reach 103731 := (sr 1 103731 155597 (by norm_num) (by norm_num) (sr 3 155597 58349 (by norm_num) (by norm_num) (B 58349 (by norm_num) (by norm_num) (by norm_num))))
theorem R103735 : Reach 103735 := (sr 1 103735 155603 (by norm_num) (by norm_num) (sr 1 155603 233405 (by norm_num) (by norm_num) (sr 3 233405 87527 (by norm_num) (by norm_num) (B 87527 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103739 : Reach 103739 := (sr 1 103739 155609 (by norm_num) (by norm_num) (sr 2 155609 116707 (by norm_num) (by norm_num) (sr 1 116707 175061 (by norm_num) (by norm_num) (sr 7 175061 4103 (by norm_num) (by norm_num) (B 4103 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103743 : Reach 103743 := (sr 1 103743 155615 (by norm_num) (by norm_num) (sr 1 155615 233423 (by norm_num) (by norm_num) (sr 1 233423 350135 (by norm_num) (by norm_num) (sr 1 350135 525203 (by norm_num) (by norm_num) (sr 1 525203 787805 (by norm_num) (by norm_num) (sr 3 787805 295427 (by norm_num) (by norm_num) (sr 1 295427 443141 (by norm_num) (by norm_num) (sr 4 443141 83089 (by norm_num) (by norm_num) (B 83089 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R103747 : Reach 103747 := (sr 1 103747 155621 (by norm_num) (by norm_num) (sr 4 155621 29179 (by norm_num) (by norm_num) (B 29179 (by norm_num) (by norm_num) (by norm_num))))
theorem R103751 : Reach 103751 := (sr 1 103751 155627 (by norm_num) (by norm_num) (sr 1 155627 233441 (by norm_num) (by norm_num) (sr 2 233441 175081 (by norm_num) (by norm_num) (sr 2 175081 131311 (by norm_num) (by norm_num) (sr 1 131311 196967 (by norm_num) (by norm_num) (sr 1 196967 295451 (by norm_num) (by norm_num) (sr 1 295451 443177 (by norm_num) (by norm_num) (sr 2 443177 332383 (by norm_num) (by norm_num) (sr 1 332383 498575 (by norm_num) (by norm_num) (sr 1 498575 747863 (by norm_num) (by norm_num) (sr 1 747863 1121795 (by norm_num) (by norm_num) (sr 1 1121795 1682693 (by norm_num) (by norm_num) (sr 4 1682693 315505 (by norm_num) (by norm_num) (sr 2 315505 236629 (by norm_num) (by norm_num) (sr 8 236629 2773 (by norm_num) (by norm_num) (B 2773 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R103755 : Reach 103755 := (sr 1 103755 155633 (by norm_num) (by norm_num) (sr 2 155633 116725 (by norm_num) (by norm_num) (sr 5 116725 10943 (by norm_num) (by norm_num) (B 10943 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103759 : Reach 103759 := (sr 1 103759 155639 (by norm_num) (by norm_num) (sr 1 155639 233459 (by norm_num) (by norm_num) (sr 1 233459 350189 (by norm_num) (by norm_num) (sr 3 350189 131321 (by norm_num) (by norm_num) (sr 2 131321 98491 (by norm_num) (by norm_num) (B 98491 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103763 : Reach 103763 := (sr 1 103763 155645 (by norm_num) (by norm_num) (sr 3 155645 58367 (by norm_num) (by norm_num) (B 58367 (by norm_num) (by norm_num) (by norm_num))))
theorem R103767 : Reach 103767 := (sr 1 103767 155651 (by norm_num) (by norm_num) (sr 1 155651 233477 (by norm_num) (by norm_num) (sr 4 233477 43777 (by norm_num) (by norm_num) (B 43777 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103771 : Reach 103771 := (sr 1 103771 155657 (by norm_num) (by norm_num) (sr 2 155657 116743 (by norm_num) (by norm_num) (sr 1 116743 175115 (by norm_num) (by norm_num) (sr 1 175115 262673 (by norm_num) (by norm_num) (sr 2 262673 197005 (by norm_num) (by norm_num) (sr 3 197005 73877 (by norm_num) (by norm_num) (B 73877 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R103775 : Reach 103775 := (sr 1 103775 155663 (by norm_num) (by norm_num) (sr 1 155663 233495 (by norm_num) (by norm_num) (sr 1 233495 350243 (by norm_num) (by norm_num) (sr 1 350243 525365 (by norm_num) (by norm_num) (sr 5 525365 49253 (by norm_num) (by norm_num) (B 49253 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103779 : Reach 103779 := (sr 1 103779 155669 (by norm_num) (by norm_num) (sr 6 155669 7297 (by norm_num) (by norm_num) (B 7297 (by norm_num) (by norm_num) (by norm_num))))
theorem R103783 : Reach 103783 := (sr 1 103783 155675 (by norm_num) (by norm_num) (sr 1 155675 233513 (by norm_num) (by norm_num) (sr 2 233513 175135 (by norm_num) (by norm_num) (sr 1 175135 262703 (by norm_num) (by norm_num) (sr 1 262703 394055 (by norm_num) (by norm_num) (sr 1 394055 591083 (by norm_num) (by norm_num) (sr 1 591083 886625 (by norm_num) (by norm_num) (sr 2 886625 664969 (by norm_num) (by norm_num) (sr 2 664969 498727 (by norm_num) (by norm_num) (sr 1 498727 748091 (by norm_num) (by norm_num) (sr 1 748091 1122137 (by norm_num) (by norm_num) (sr 2 1122137 841603 (by norm_num) (by norm_num) (sr 1 841603 1262405 (by norm_num) (by norm_num) (sr 4 1262405 236701 (by norm_num) (by norm_num) (sr 3 236701 88763 (by norm_num) (by norm_num) (B 88763 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R103787 : Reach 103787 := (sr 1 103787 155681 (by norm_num) (by norm_num) (sr 2 155681 116761 (by norm_num) (by norm_num) (sr 2 116761 87571 (by norm_num) (by norm_num) (B 87571 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103791 : Reach 103791 := (sr 1 103791 155687 (by norm_num) (by norm_num) (sr 1 155687 233531 (by norm_num) (by norm_num) (sr 1 233531 350297 (by norm_num) (by norm_num) (sr 2 350297 262723 (by norm_num) (by norm_num) (sr 1 262723 394085 (by norm_num) (by norm_num) (sr 4 394085 73891 (by norm_num) (by norm_num) (B 73891 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R103795 : Reach 103795 := (sr 1 103795 155693 (by norm_num) (by norm_num) (sr 3 155693 58385 (by norm_num) (by norm_num) (B 58385 (by norm_num) (by norm_num) (by norm_num))))
theorem R103799 : Reach 103799 := (sr 1 103799 155699 (by norm_num) (by norm_num) (sr 1 155699 233549 (by norm_num) (by norm_num) (sr 3 233549 87581 (by norm_num) (by norm_num) (B 87581 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103803 : Reach 103803 := (sr 1 103803 155705 (by norm_num) (by norm_num) (sr 2 155705 116779 (by norm_num) (by norm_num) (sr 1 116779 175169 (by norm_num) (by norm_num) (sr 2 175169 131377 (by norm_num) (by norm_num) (sr 2 131377 98533 (by norm_num) (by norm_num) (B 98533 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103807 : Reach 103807 := (sr 1 103807 155711 (by norm_num) (by norm_num) (sr 1 155711 233567 (by norm_num) (by norm_num) (sr 1 233567 350351 (by norm_num) (by norm_num) (sr 1 350351 525527 (by norm_num) (by norm_num) (sr 1 525527 788291 (by norm_num) (by norm_num) (sr 1 788291 1182437 (by norm_num) (by norm_num) (sr 4 1182437 221707 (by norm_num) (by norm_num) (sr 1 221707 332561 (by norm_num) (by norm_num) (sr 2 332561 249421 (by norm_num) (by norm_num) (sr 3 249421 93533 (by norm_num) (by norm_num) (B 93533 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R103811 : Reach 103811 := (sr 1 103811 155717 (by norm_num) (by norm_num) (sr 4 155717 29197 (by norm_num) (by norm_num) (B 29197 (by norm_num) (by norm_num) (by norm_num))))
theorem R103815 : Reach 103815 := (sr 1 103815 155723 (by norm_num) (by norm_num) (sr 1 155723 233585 (by norm_num) (by norm_num) (sr 2 233585 175189 (by norm_num) (by norm_num) (sr 8 175189 2053 (by norm_num) (by norm_num) (B 2053 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103819 : Reach 103819 := (sr 1 103819 155729 (by norm_num) (by norm_num) (sr 2 155729 116797 (by norm_num) (by norm_num) (sr 3 116797 43799 (by norm_num) (by norm_num) (B 43799 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103823 : Reach 103823 := (sr 1 103823 155735 (by norm_num) (by norm_num) (sr 1 155735 233603 (by norm_num) (by norm_num) (sr 1 233603 350405 (by norm_num) (by norm_num) (sr 4 350405 65701 (by norm_num) (by norm_num) (B 65701 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103827 : Reach 103827 := (sr 1 103827 155741 (by norm_num) (by norm_num) (sr 3 155741 58403 (by norm_num) (by norm_num) (B 58403 (by norm_num) (by norm_num) (by norm_num))))
theorem R103831 : Reach 103831 := (sr 1 103831 155747 (by norm_num) (by norm_num) (sr 1 155747 233621 (by norm_num) (by norm_num) (sr 6 233621 10951 (by norm_num) (by norm_num) (B 10951 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103835 : Reach 103835 := (sr 1 103835 155753 (by norm_num) (by norm_num) (sr 2 155753 116815 (by norm_num) (by norm_num) (sr 1 116815 175223 (by norm_num) (by norm_num) (sr 1 175223 262835 (by norm_num) (by norm_num) (sr 1 262835 394253 (by norm_num) (by norm_num) (sr 3 394253 147845 (by norm_num) (by norm_num) (sr 4 147845 27721 (by norm_num) (by norm_num) (B 27721 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R103839 : Reach 103839 := (sr 1 103839 155759 (by norm_num) (by norm_num) (sr 1 155759 233639 (by norm_num) (by norm_num) (sr 1 233639 350459 (by norm_num) (by norm_num) (sr 1 350459 525689 (by norm_num) (by norm_num) (sr 2 525689 394267 (by norm_num) (by norm_num) (sr 1 394267 591401 (by norm_num) (by norm_num) (sr 2 591401 443551 (by norm_num) (by norm_num) (sr 1 443551 665327 (by norm_num) (by norm_num) (sr 1 665327 997991 (by norm_num) (by norm_num) (sr 1 997991 1496987 (by norm_num) (by norm_num) (sr 1 1496987 2245481 (by norm_num) (by norm_num) (sr 2 2245481 1684111 (by norm_num) (by norm_num) (sr 1 1684111 2526167 (by norm_num) (by norm_num) (sr 1 2526167 3789251 (by norm_num) (by norm_num) (sr 1 3789251 5683877 (by norm_num) (by norm_num) (sr 4 5683877 1065727 (by norm_num) (by norm_num) (sr 1 1065727 1598591 (by norm_num) (by norm_num) (sr 1 1598591 2397887 (by norm_num) (by norm_num) (sr 1 2397887 3596831 (by norm_num) (by norm_num) (sr 1 3596831 5395247 (by norm_num) (by norm_num) (sr 1 5395247 8092871 (by norm_num) (by norm_num) (sr 1 8092871 12139307 (by norm_num) (by norm_num) (sr 1 12139307 18208961 (by norm_num) (by norm_num) (sr 2 18208961 13656721 (by norm_num) (by norm_num) (sr 2 13656721 10242541 (by norm_num) (by norm_num) (sr 3 10242541 3840953 (by norm_num) (by norm_num) (sr 2 3840953 2880715 (by norm_num) (by norm_num) (sr 1 2880715 4321073 (by norm_num) (by norm_num) (sr 2 4321073 3240805 (by norm_num) (by norm_num) (sr 4 3240805 607651 (by norm_num) (by norm_num) (sr 1 607651 911477 (by norm_num) (by norm_num) (sr 5 911477 85451 (by norm_num) (by norm_num) (B 85451 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))))))
theorem R103843 : Reach 103843 := (sr 1 103843 155765 (by norm_num) (by norm_num) (sr 5 155765 14603 (by norm_num) (by norm_num) (B 14603 (by norm_num) (by norm_num) (by norm_num))))
theorem R103847 : Reach 103847 := (sr 1 103847 155771 (by norm_num) (by norm_num) (sr 1 155771 233657 (by norm_num) (by norm_num) (sr 2 233657 175243 (by norm_num) (by norm_num) (sr 1 175243 262865 (by norm_num) (by norm_num) (sr 2 262865 197149 (by norm_num) (by norm_num) (sr 3 197149 73931 (by norm_num) (by norm_num) (B 73931 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R103851 : Reach 103851 := (sr 1 103851 155777 (by norm_num) (by norm_num) (sr 2 155777 116833 (by norm_num) (by norm_num) (sr 2 116833 87625 (by norm_num) (by norm_num) (B 87625 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103855 : Reach 103855 := (sr 1 103855 155783 (by norm_num) (by norm_num) (sr 1 155783 233675 (by norm_num) (by norm_num) (sr 1 233675 350513 (by norm_num) (by norm_num) (sr 2 350513 262885 (by norm_num) (by norm_num) (sr 4 262885 49291 (by norm_num) (by norm_num) (B 49291 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103859 : Reach 103859 := (sr 1 103859 155789 (by norm_num) (by norm_num) (sr 3 155789 58421 (by norm_num) (by norm_num) (B 58421 (by norm_num) (by norm_num) (by norm_num))))
theorem R103863 : Reach 103863 := (sr 1 103863 155795 (by norm_num) (by norm_num) (sr 1 155795 233693 (by norm_num) (by norm_num) (sr 3 233693 87635 (by norm_num) (by norm_num) (B 87635 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103867 : Reach 103867 := (sr 1 103867 155801 (by norm_num) (by norm_num) (sr 2 155801 116851 (by norm_num) (by norm_num) (sr 1 116851 175277 (by norm_num) (by norm_num) (sr 3 175277 65729 (by norm_num) (by norm_num) (B 65729 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103871 : Reach 103871 := (sr 1 103871 155807 (by norm_num) (by norm_num) (sr 1 155807 233711 (by norm_num) (by norm_num) (sr 1 233711 350567 (by norm_num) (by norm_num) (sr 1 350567 525851 (by norm_num) (by norm_num) (sr 1 525851 788777 (by norm_num) (by norm_num) (sr 2 788777 591583 (by norm_num) (by norm_num) (sr 1 591583 887375 (by norm_num) (by norm_num) (sr 1 887375 1331063 (by norm_num) (by norm_num) (sr 1 1331063 1996595 (by norm_num) (by norm_num) (sr 1 1996595 2994893 (by norm_num) (by norm_num) (sr 3 2994893 1123085 (by norm_num) (by norm_num) (sr 3 1123085 421157 (by norm_num) (by norm_num) (sr 4 421157 78967 (by norm_num) (by norm_num) (B 78967 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R103875 : Reach 103875 := (sr 1 103875 155813 (by norm_num) (by norm_num) (sr 4 155813 29215 (by norm_num) (by norm_num) (B 29215 (by norm_num) (by norm_num) (by norm_num))))
theorem R103879 : Reach 103879 := (sr 1 103879 155819 (by norm_num) (by norm_num) (sr 1 155819 233729 (by norm_num) (by norm_num) (sr 2 233729 175297 (by norm_num) (by norm_num) (sr 2 175297 131473 (by norm_num) (by norm_num) (sr 2 131473 98605 (by norm_num) (by norm_num) (B 98605 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103883 : Reach 103883 := (sr 1 103883 155825 (by norm_num) (by norm_num) (sr 2 155825 116869 (by norm_num) (by norm_num) (sr 4 116869 21913 (by norm_num) (by norm_num) (B 21913 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103887 : Reach 103887 := (sr 1 103887 155831 (by norm_num) (by norm_num) (sr 1 155831 233747 (by norm_num) (by norm_num) (sr 1 233747 350621 (by norm_num) (by norm_num) (sr 3 350621 131483 (by norm_num) (by norm_num) (sr 1 131483 197225 (by norm_num) (by norm_num) (sr 2 197225 147919 (by norm_num) (by norm_num) (sr 1 147919 221879 (by norm_num) (by norm_num) (sr 1 221879 332819 (by norm_num) (by norm_num) (sr 1 332819 499229 (by norm_num) (by norm_num) (sr 3 499229 187211 (by norm_num) (by norm_num) (sr 1 187211 280817 (by norm_num) (by norm_num) (sr 2 280817 210613 (by norm_num) (by norm_num) (sr 5 210613 19745 (by norm_num) (by norm_num) (B 19745 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R103891 : Reach 103891 := (sr 1 103891 155837 (by norm_num) (by norm_num) (sr 3 155837 58439 (by norm_num) (by norm_num) (B 58439 (by norm_num) (by norm_num) (by norm_num))))
theorem R103895 : Reach 103895 := (sr 1 103895 155843 (by norm_num) (by norm_num) (sr 1 155843 233765 (by norm_num) (by norm_num) (sr 4 233765 43831 (by norm_num) (by norm_num) (B 43831 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103899 : Reach 103899 := (sr 1 103899 155849 (by norm_num) (by norm_num) (sr 2 155849 116887 (by norm_num) (by norm_num) (sr 1 116887 175331 (by norm_num) (by norm_num) (sr 1 175331 262997 (by norm_num) (by norm_num) (sr 9 262997 1541 (by norm_num) (by norm_num) (B 1541 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103903 : Reach 103903 := (sr 1 103903 155855 (by norm_num) (by norm_num) (sr 1 155855 233783 (by norm_num) (by norm_num) (sr 1 233783 350675 (by norm_num) (by norm_num) (sr 1 350675 526013 (by norm_num) (by norm_num) (sr 3 526013 197255 (by norm_num) (by norm_num) (sr 1 197255 295883 (by norm_num) (by norm_num) (sr 1 295883 443825 (by norm_num) (by norm_num) (sr 2 443825 332869 (by norm_num) (by norm_num) (sr 4 332869 62413 (by norm_num) (by norm_num) (B 62413 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R103907 : Reach 103907 := (sr 1 103907 155861 (by norm_num) (by norm_num) (sr 7 155861 3653 (by norm_num) (by norm_num) (B 3653 (by norm_num) (by norm_num) (by norm_num))))
theorem R103911 : Reach 103911 := (sr 1 103911 155867 (by norm_num) (by norm_num) (sr 1 155867 233801 (by norm_num) (by norm_num) (sr 2 233801 175351 (by norm_num) (by norm_num) (sr 1 175351 263027 (by norm_num) (by norm_num) (sr 1 263027 394541 (by norm_num) (by norm_num) (sr 3 394541 147953 (by norm_num) (by norm_num) (sr 2 147953 110965 (by norm_num) (by norm_num) (sr 5 110965 10403 (by norm_num) (by norm_num) (B 10403 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R103915 : Reach 103915 := (sr 1 103915 155873 (by norm_num) (by norm_num) (sr 2 155873 116905 (by norm_num) (by norm_num) (sr 2 116905 87679 (by norm_num) (by norm_num) (B 87679 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103919 : Reach 103919 := (sr 1 103919 155879 (by norm_num) (by norm_num) (sr 1 155879 233819 (by norm_num) (by norm_num) (sr 1 233819 350729 (by norm_num) (by norm_num) (sr 2 350729 263047 (by norm_num) (by norm_num) (sr 1 263047 394571 (by norm_num) (by norm_num) (sr 1 394571 591857 (by norm_num) (by norm_num) (sr 2 591857 443893 (by norm_num) (by norm_num) (sr 5 443893 41615 (by norm_num) (by norm_num) (B 41615 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R103923 : Reach 103923 := (sr 1 103923 155885 (by norm_num) (by norm_num) (sr 3 155885 58457 (by norm_num) (by norm_num) (B 58457 (by norm_num) (by norm_num) (by norm_num))))
theorem R103927 : Reach 103927 := (sr 1 103927 155891 (by norm_num) (by norm_num) (sr 1 155891 233837 (by norm_num) (by norm_num) (sr 3 233837 87689 (by norm_num) (by norm_num) (B 87689 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103931 : Reach 103931 := (sr 1 103931 155897 (by norm_num) (by norm_num) (sr 2 155897 116923 (by norm_num) (by norm_num) (sr 1 116923 175385 (by norm_num) (by norm_num) (sr 2 175385 131539 (by norm_num) (by norm_num) (sr 1 131539 197309 (by norm_num) (by norm_num) (sr 3 197309 73991 (by norm_num) (by norm_num) (B 73991 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R103935 : Reach 103935 := (sr 1 103935 155903 (by norm_num) (by norm_num) (sr 1 155903 233855 (by norm_num) (by norm_num) (sr 1 233855 350783 (by norm_num) (by norm_num) (sr 1 350783 526175 (by norm_num) (by norm_num) (sr 1 526175 789263 (by norm_num) (by norm_num) (sr 1 789263 1183895 (by norm_num) (by norm_num) (sr 1 1183895 1775843 (by norm_num) (by norm_num) (sr 1 1775843 2663765 (by norm_num) (by norm_num) (sr 12 2663765 1951 (by norm_num) (by norm_num) (B 1951 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R103939 : Reach 103939 := (sr 1 103939 155909 (by norm_num) (by norm_num) (sr 4 155909 29233 (by norm_num) (by norm_num) (B 29233 (by norm_num) (by norm_num) (by norm_num))))
theorem R103943 : Reach 103943 := (sr 1 103943 155915 (by norm_num) (by norm_num) (sr 1 155915 233873 (by norm_num) (by norm_num) (sr 2 233873 175405 (by norm_num) (by norm_num) (sr 3 175405 65777 (by norm_num) (by norm_num) (B 65777 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103947 : Reach 103947 := (sr 1 103947 155921 (by norm_num) (by norm_num) (sr 2 155921 116941 (by norm_num) (by norm_num) (sr 3 116941 43853 (by norm_num) (by norm_num) (B 43853 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103951 : Reach 103951 := (sr 1 103951 155927 (by norm_num) (by norm_num) (sr 1 155927 233891 (by norm_num) (by norm_num) (sr 1 233891 350837 (by norm_num) (by norm_num) (sr 5 350837 32891 (by norm_num) (by norm_num) (B 32891 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103955 : Reach 103955 := (sr 1 103955 155933 (by norm_num) (by norm_num) (sr 3 155933 58475 (by norm_num) (by norm_num) (B 58475 (by norm_num) (by norm_num) (by norm_num))))
theorem R103959 : Reach 103959 := (sr 1 103959 155939 (by norm_num) (by norm_num) (sr 1 155939 233909 (by norm_num) (by norm_num) (sr 5 233909 21929 (by norm_num) (by norm_num) (B 21929 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103963 : Reach 103963 := (sr 1 103963 155945 (by norm_num) (by norm_num) (sr 2 155945 116959 (by norm_num) (by norm_num) (sr 1 116959 175439 (by norm_num) (by norm_num) (sr 1 175439 263159 (by norm_num) (by norm_num) (sr 1 263159 394739 (by norm_num) (by norm_num) (sr 1 394739 592109 (by norm_num) (by norm_num) (sr 3 592109 222041 (by norm_num) (by norm_num) (sr 2 222041 166531 (by norm_num) (by norm_num) (sr 1 166531 249797 (by norm_num) (by norm_num) (sr 4 249797 46837 (by norm_num) (by norm_num) (B 46837 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R103967 : Reach 103967 := (sr 1 103967 155951 (by norm_num) (by norm_num) (sr 1 155951 233927 (by norm_num) (by norm_num) (sr 1 233927 350891 (by norm_num) (by norm_num) (sr 1 350891 526337 (by norm_num) (by norm_num) (sr 2 526337 394753 (by norm_num) (by norm_num) (sr 2 394753 296065 (by norm_num) (by norm_num) (sr 2 296065 222049 (by norm_num) (by norm_num) (sr 2 222049 166537 (by norm_num) (by norm_num) (sr 2 166537 124903 (by norm_num) (by norm_num) (sr 1 124903 187355 (by norm_num) (by norm_num) (sr 1 187355 281033 (by norm_num) (by norm_num) (sr 2 281033 210775 (by norm_num) (by norm_num) (sr 1 210775 316163 (by norm_num) (by norm_num) (sr 1 316163 474245 (by norm_num) (by norm_num) (sr 4 474245 88921 (by norm_num) (by norm_num) (B 88921 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R103971 : Reach 103971 := (sr 1 103971 155957 (by norm_num) (by norm_num) (sr 5 155957 14621 (by norm_num) (by norm_num) (B 14621 (by norm_num) (by norm_num) (by norm_num))))
theorem R103975 : Reach 103975 := (sr 1 103975 155963 (by norm_num) (by norm_num) (sr 1 155963 233945 (by norm_num) (by norm_num) (sr 2 233945 175459 (by norm_num) (by norm_num) (sr 1 175459 263189 (by norm_num) (by norm_num) (sr 6 263189 12337 (by norm_num) (by norm_num) (B 12337 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R103979 : Reach 103979 := (sr 1 103979 155969 (by norm_num) (by norm_num) (sr 2 155969 116977 (by norm_num) (by norm_num) (sr 2 116977 87733 (by norm_num) (by norm_num) (B 87733 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103983 : Reach 103983 := (sr 1 103983 155975 (by norm_num) (by norm_num) (sr 1 155975 233963 (by norm_num) (by norm_num) (sr 1 233963 350945 (by norm_num) (by norm_num) (sr 2 350945 263209 (by norm_num) (by norm_num) (sr 2 263209 197407 (by norm_num) (by norm_num) (sr 1 197407 296111 (by norm_num) (by norm_num) (sr 1 296111 444167 (by norm_num) (by norm_num) (sr 1 444167 666251 (by norm_num) (by norm_num) (sr 1 666251 999377 (by norm_num) (by norm_num) (sr 2 999377 749533 (by norm_num) (by norm_num) (sr 3 749533 281075 (by norm_num) (by norm_num) (sr 1 281075 421613 (by norm_num) (by norm_num) (sr 3 421613 158105 (by norm_num) (by norm_num) (sr 2 158105 118579 (by norm_num) (by norm_num) (sr 1 118579 177869 (by norm_num) (by norm_num) (sr 3 177869 66701 (by norm_num) (by norm_num) (B 66701 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))
theorem R103987 : Reach 103987 := (sr 1 103987 155981 (by norm_num) (by norm_num) (sr 3 155981 58493 (by norm_num) (by norm_num) (B 58493 (by norm_num) (by norm_num) (by norm_num))))
theorem R103991 : Reach 103991 := (sr 1 103991 155987 (by norm_num) (by norm_num) (sr 1 155987 233981 (by norm_num) (by norm_num) (sr 3 233981 87743 (by norm_num) (by norm_num) (B 87743 (by norm_num) (by norm_num) (by norm_num)))))
theorem R103995 : Reach 103995 := (sr 1 103995 155993 (by norm_num) (by norm_num) (sr 2 155993 116995 (by norm_num) (by norm_num) (sr 1 116995 175493 (by norm_num) (by norm_num) (sr 4 175493 32905 (by norm_num) (by norm_num) (B 32905 (by norm_num) (by norm_num) (by norm_num))))))
theorem R103999 : Reach 103999 := (sr 1 103999 155999 (by norm_num) (by norm_num) (sr 1 155999 233999 (by norm_num) (by norm_num) (sr 1 233999 350999 (by norm_num) (by norm_num) (sr 1 350999 526499 (by norm_num) (by norm_num) (sr 1 526499 789749 (by norm_num) (by norm_num) (sr 5 789749 74039 (by norm_num) (by norm_num) (B 74039 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R104003 : Reach 104003 := (sr 1 104003 156005 (by norm_num) (by norm_num) (sr 4 156005 29251 (by norm_num) (by norm_num) (B 29251 (by norm_num) (by norm_num) (by norm_num))))
theorem R104007 : Reach 104007 := (sr 1 104007 156011 (by norm_num) (by norm_num) (sr 1 156011 234017 (by norm_num) (by norm_num) (sr 2 234017 175513 (by norm_num) (by norm_num) (sr 2 175513 131635 (by norm_num) (by norm_num) (sr 1 131635 197453 (by norm_num) (by norm_num) (sr 3 197453 74045 (by norm_num) (by norm_num) (B 74045 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R104011 : Reach 104011 := (sr 1 104011 156017 (by norm_num) (by norm_num) (sr 2 156017 117013 (by norm_num) (by norm_num) (sr 6 117013 5485 (by norm_num) (by norm_num) (B 5485 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104015 : Reach 104015 := (sr 1 104015 156023 (by norm_num) (by norm_num) (sr 1 156023 234035 (by norm_num) (by norm_num) (sr 1 234035 351053 (by norm_num) (by norm_num) (sr 3 351053 131645 (by norm_num) (by norm_num) (sr 3 131645 49367 (by norm_num) (by norm_num) (B 49367 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104019 : Reach 104019 := (sr 1 104019 156029 (by norm_num) (by norm_num) (sr 3 156029 58511 (by norm_num) (by norm_num) (B 58511 (by norm_num) (by norm_num) (by norm_num))))
theorem R104023 : Reach 104023 := (sr 1 104023 156035 (by norm_num) (by norm_num) (sr 1 156035 234053 (by norm_num) (by norm_num) (sr 4 234053 43885 (by norm_num) (by norm_num) (B 43885 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104027 : Reach 104027 := (sr 1 104027 156041 (by norm_num) (by norm_num) (sr 2 156041 117031 (by norm_num) (by norm_num) (sr 1 117031 175547 (by norm_num) (by norm_num) (sr 1 175547 263321 (by norm_num) (by norm_num) (sr 2 263321 197491 (by norm_num) (by norm_num) (sr 1 197491 296237 (by norm_num) (by norm_num) (sr 3 296237 111089 (by norm_num) (by norm_num) (sr 2 111089 83317 (by norm_num) (by norm_num) (B 83317 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R104031 : Reach 104031 := (sr 1 104031 156047 (by norm_num) (by norm_num) (sr 1 156047 234071 (by norm_num) (by norm_num) (sr 1 234071 351107 (by norm_num) (by norm_num) (sr 1 351107 526661 (by norm_num) (by norm_num) (sr 4 526661 98749 (by norm_num) (by norm_num) (B 98749 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104035 : Reach 104035 := (sr 1 104035 156053 (by norm_num) (by norm_num) (sr 6 156053 7315 (by norm_num) (by norm_num) (B 7315 (by norm_num) (by norm_num) (by norm_num))))
theorem R104039 : Reach 104039 := (sr 1 104039 156059 (by norm_num) (by norm_num) (sr 1 156059 234089 (by norm_num) (by norm_num) (sr 2 234089 175567 (by norm_num) (by norm_num) (sr 1 175567 263351 (by norm_num) (by norm_num) (sr 1 263351 395027 (by norm_num) (by norm_num) (sr 1 395027 592541 (by norm_num) (by norm_num) (sr 3 592541 222203 (by norm_num) (by norm_num) (sr 1 222203 333305 (by norm_num) (by norm_num) (sr 2 333305 249979 (by norm_num) (by norm_num) (sr 1 249979 374969 (by norm_num) (by norm_num) (sr 2 374969 281227 (by norm_num) (by norm_num) (sr 1 281227 421841 (by norm_num) (by norm_num) (sr 2 421841 316381 (by norm_num) (by norm_num) (sr 3 316381 118643 (by norm_num) (by norm_num) (sr 1 118643 177965 (by norm_num) (by norm_num) (sr 3 177965 66737 (by norm_num) (by norm_num) (B 66737 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))
theorem R104043 : Reach 104043 := (sr 1 104043 156065 (by norm_num) (by norm_num) (sr 2 156065 117049 (by norm_num) (by norm_num) (sr 2 117049 87787 (by norm_num) (by norm_num) (B 87787 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104047 : Reach 104047 := (sr 1 104047 156071 (by norm_num) (by norm_num) (sr 1 156071 234107 (by norm_num) (by norm_num) (sr 1 234107 351161 (by norm_num) (by norm_num) (sr 2 351161 263371 (by norm_num) (by norm_num) (sr 1 263371 395057 (by norm_num) (by norm_num) (sr 2 395057 296293 (by norm_num) (by norm_num) (sr 4 296293 55555 (by norm_num) (by norm_num) (B 55555 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R104051 : Reach 104051 := (sr 1 104051 156077 (by norm_num) (by norm_num) (sr 3 156077 58529 (by norm_num) (by norm_num) (B 58529 (by norm_num) (by norm_num) (by norm_num))))
theorem R104055 : Reach 104055 := (sr 1 104055 156083 (by norm_num) (by norm_num) (sr 1 156083 234125 (by norm_num) (by norm_num) (sr 3 234125 87797 (by norm_num) (by norm_num) (B 87797 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104059 : Reach 104059 := (sr 1 104059 156089 (by norm_num) (by norm_num) (sr 2 156089 117067 (by norm_num) (by norm_num) (sr 1 117067 175601 (by norm_num) (by norm_num) (sr 2 175601 131701 (by norm_num) (by norm_num) (sr 5 131701 12347 (by norm_num) (by norm_num) (B 12347 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104063 : Reach 104063 := (sr 1 104063 156095 (by norm_num) (by norm_num) (sr 1 156095 234143 (by norm_num) (by norm_num) (sr 1 234143 351215 (by norm_num) (by norm_num) (sr 1 351215 526823 (by norm_num) (by norm_num) (sr 1 526823 790235 (by norm_num) (by norm_num) (sr 1 790235 1185353 (by norm_num) (by norm_num) (sr 2 1185353 889015 (by norm_num) (by norm_num) (sr 1 889015 1333523 (by norm_num) (by norm_num) (sr 1 1333523 2000285 (by norm_num) (by norm_num) (sr 3 2000285 750107 (by norm_num) (by norm_num) (sr 1 750107 1125161 (by norm_num) (by norm_num) (sr 2 1125161 843871 (by norm_num) (by norm_num) (sr 1 843871 1265807 (by norm_num) (by norm_num) (sr 1 1265807 1898711 (by norm_num) (by norm_num) (sr 1 1898711 2848067 (by norm_num) (by norm_num) (sr 1 2848067 4272101 (by norm_num) (by norm_num) (sr 4 4272101 801019 (by norm_num) (by norm_num) (sr 1 801019 1201529 (by norm_num) (by norm_num) (sr 2 1201529 901147 (by norm_num) (by norm_num) (sr 1 901147 1351721 (by norm_num) (by norm_num) (sr 2 1351721 1013791 (by norm_num) (by norm_num) (sr 1 1013791 1520687 (by norm_num) (by norm_num) (sr 1 1520687 2281031 (by norm_num) (by norm_num) (sr 1 2281031 3421547 (by norm_num) (by norm_num) (sr 1 3421547 5132321 (by norm_num) (by norm_num) (sr 2 5132321 3849241 (by norm_num) (by norm_num) (sr 2 3849241 2886931 (by norm_num) (by norm_num) (sr 1 2886931 4330397 (by norm_num) (by norm_num) (sr 3 4330397 1623899 (by norm_num) (by norm_num) (sr 1 1623899 2435849 (by norm_num) (by norm_num) (sr 2 2435849 1826887 (by norm_num) (by norm_num) (sr 1 1826887 2740331 (by norm_num) (by norm_num) (sr 1 2740331 4110497 (by norm_num) (by norm_num) (sr 2 4110497 3082873 (by norm_num) (by norm_num) (sr 2 3082873 2312155 (by norm_num) (by norm_num) (sr 1 2312155 3468233 (by norm_num) (by norm_num) (sr 2 3468233 2601175 (by norm_num) (by norm_num) (sr 1 2601175 3901763 (by norm_num) (by norm_num) (sr 1 3901763 5852645 (by norm_num) (by norm_num) (sr 4 5852645 1097371 (by norm_num) (by norm_num) (sr 1 1097371 1646057 (by norm_num) (by norm_num) (sr 2 1646057 1234543 (by norm_num) (by norm_num) (sr 1 1234543 1851815 (by norm_num) (by norm_num) (sr 1 1851815 2777723 (by norm_num) (by norm_num) (sr 1 2777723 4166585 (by norm_num) (by norm_num) (sr 2 4166585 3124939 (by norm_num) (by norm_num) (sr 1 3124939 4687409 (by norm_num) (by norm_num) (sr 2 4687409 3515557 (by norm_num) (by norm_num) (sr 4 3515557 659167 (by norm_num) (by norm_num) (sr 1 659167 988751 (by norm_num) (by norm_num) (sr 1 988751 1483127 (by norm_num) (by norm_num) (sr 1 1483127 2224691 (by norm_num) (by norm_num) (sr 1 2224691 3337037 (by norm_num) (by norm_num) (sr 3 3337037 1251389 (by norm_num) (by norm_num) (sr 3 1251389 469271 (by norm_num) (by norm_num) (sr 1 469271 703907 (by norm_num) (by norm_num) (sr 1 703907 1055861 (by norm_num) (by norm_num) (sr 5 1055861 98987 (by norm_num) (by norm_num) (B 98987 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem R104067 : Reach 104067 := (sr 1 104067 156101 (by norm_num) (by norm_num) (sr 4 156101 29269 (by norm_num) (by norm_num) (B 29269 (by norm_num) (by norm_num) (by norm_num))))
theorem R104071 : Reach 104071 := (sr 1 104071 156107 (by norm_num) (by norm_num) (sr 1 156107 234161 (by norm_num) (by norm_num) (sr 2 234161 175621 (by norm_num) (by norm_num) (sr 4 175621 32929 (by norm_num) (by norm_num) (B 32929 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104075 : Reach 104075 := (sr 1 104075 156113 (by norm_num) (by norm_num) (sr 2 156113 117085 (by norm_num) (by norm_num) (sr 3 117085 43907 (by norm_num) (by norm_num) (B 43907 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104079 : Reach 104079 := (sr 1 104079 156119 (by norm_num) (by norm_num) (sr 1 156119 234179 (by norm_num) (by norm_num) (sr 1 234179 351269 (by norm_num) (by norm_num) (sr 4 351269 65863 (by norm_num) (by norm_num) (B 65863 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104083 : Reach 104083 := (sr 1 104083 156125 (by norm_num) (by norm_num) (sr 3 156125 58547 (by norm_num) (by norm_num) (B 58547 (by norm_num) (by norm_num) (by norm_num))))
theorem R104087 : Reach 104087 := (sr 1 104087 156131 (by norm_num) (by norm_num) (sr 1 156131 234197 (by norm_num) (by norm_num) (sr 7 234197 5489 (by norm_num) (by norm_num) (B 5489 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104091 : Reach 104091 := (sr 1 104091 156137 (by norm_num) (by norm_num) (sr 2 156137 117103 (by norm_num) (by norm_num) (sr 1 117103 175655 (by norm_num) (by norm_num) (sr 1 175655 263483 (by norm_num) (by norm_num) (sr 1 263483 395225 (by norm_num) (by norm_num) (sr 2 395225 296419 (by norm_num) (by norm_num) (sr 1 296419 444629 (by norm_num) (by norm_num) (sr 7 444629 10421 (by norm_num) (by norm_num) (B 10421 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R104095 : Reach 104095 := (sr 1 104095 156143 (by norm_num) (by norm_num) (sr 1 156143 234215 (by norm_num) (by norm_num) (sr 1 234215 351323 (by norm_num) (by norm_num) (sr 1 351323 526985 (by norm_num) (by norm_num) (sr 2 526985 395239 (by norm_num) (by norm_num) (sr 1 395239 592859 (by norm_num) (by norm_num) (sr 1 592859 889289 (by norm_num) (by norm_num) (sr 2 889289 666967 (by norm_num) (by norm_num) (sr 1 666967 1000451 (by norm_num) (by norm_num) (sr 1 1000451 1500677 (by norm_num) (by norm_num) (sr 4 1500677 281377 (by norm_num) (by norm_num) (sr 2 281377 211033 (by norm_num) (by norm_num) (sr 2 211033 158275 (by norm_num) (by norm_num) (sr 1 158275 237413 (by norm_num) (by norm_num) (sr 4 237413 44515 (by norm_num) (by norm_num) (B 44515 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R104099 : Reach 104099 := (sr 1 104099 156149 (by norm_num) (by norm_num) (sr 5 156149 14639 (by norm_num) (by norm_num) (B 14639 (by norm_num) (by norm_num) (by norm_num))))
theorem R104103 : Reach 104103 := (sr 1 104103 156155 (by norm_num) (by norm_num) (sr 1 156155 234233 (by norm_num) (by norm_num) (sr 2 234233 175675 (by norm_num) (by norm_num) (sr 1 175675 263513 (by norm_num) (by norm_num) (sr 2 263513 197635 (by norm_num) (by norm_num) (sr 1 197635 296453 (by norm_num) (by norm_num) (sr 4 296453 55585 (by norm_num) (by norm_num) (B 55585 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R104107 : Reach 104107 := (sr 1 104107 156161 (by norm_num) (by norm_num) (sr 2 156161 117121 (by norm_num) (by norm_num) (sr 2 117121 87841 (by norm_num) (by norm_num) (B 87841 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104111 : Reach 104111 := (sr 1 104111 156167 (by norm_num) (by norm_num) (sr 1 156167 234251 (by norm_num) (by norm_num) (sr 1 234251 351377 (by norm_num) (by norm_num) (sr 2 351377 263533 (by norm_num) (by norm_num) (sr 3 263533 98825 (by norm_num) (by norm_num) (B 98825 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104115 : Reach 104115 := (sr 1 104115 156173 (by norm_num) (by norm_num) (sr 3 156173 58565 (by norm_num) (by norm_num) (B 58565 (by norm_num) (by norm_num) (by norm_num))))
theorem R104119 : Reach 104119 := (sr 1 104119 156179 (by norm_num) (by norm_num) (sr 1 156179 234269 (by norm_num) (by norm_num) (sr 3 234269 87851 (by norm_num) (by norm_num) (B 87851 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104123 : Reach 104123 := (sr 1 104123 156185 (by norm_num) (by norm_num) (sr 2 156185 117139 (by norm_num) (by norm_num) (sr 1 117139 175709 (by norm_num) (by norm_num) (sr 3 175709 65891 (by norm_num) (by norm_num) (B 65891 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104127 : Reach 104127 := (sr 1 104127 156191 (by norm_num) (by norm_num) (sr 1 156191 234287 (by norm_num) (by norm_num) (sr 1 234287 351431 (by norm_num) (by norm_num) (sr 1 351431 527147 (by norm_num) (by norm_num) (sr 1 527147 790721 (by norm_num) (by norm_num) (sr 2 790721 593041 (by norm_num) (by norm_num) (sr 2 593041 444781 (by norm_num) (by norm_num) (sr 3 444781 166793 (by norm_num) (by norm_num) (sr 2 166793 125095 (by norm_num) (by norm_num) (sr 1 125095 187643 (by norm_num) (by norm_num) (sr 1 187643 281465 (by norm_num) (by norm_num) (sr 2 281465 211099 (by norm_num) (by norm_num) (sr 1 211099 316649 (by norm_num) (by norm_num) (sr 2 316649 237487 (by norm_num) (by norm_num) (sr 1 237487 356231 (by norm_num) (by norm_num) (sr 1 356231 534347 (by norm_num) (by norm_num) (sr 1 534347 801521 (by norm_num) (by norm_num) (sr 2 801521 601141 (by norm_num) (by norm_num) (sr 5 601141 56357 (by norm_num) (by norm_num) (B 56357 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))
theorem R104131 : Reach 104131 := (sr 1 104131 156197 (by norm_num) (by norm_num) (sr 4 156197 29287 (by norm_num) (by norm_num) (B 29287 (by norm_num) (by norm_num) (by norm_num))))
theorem R104135 : Reach 104135 := (sr 1 104135 156203 (by norm_num) (by norm_num) (sr 1 156203 234305 (by norm_num) (by norm_num) (sr 2 234305 175729 (by norm_num) (by norm_num) (sr 2 175729 131797 (by norm_num) (by norm_num) (sr 7 131797 3089 (by norm_num) (by norm_num) (B 3089 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104139 : Reach 104139 := (sr 1 104139 156209 (by norm_num) (by norm_num) (sr 2 156209 117157 (by norm_num) (by norm_num) (sr 4 117157 21967 (by norm_num) (by norm_num) (B 21967 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104143 : Reach 104143 := (sr 1 104143 156215 (by norm_num) (by norm_num) (sr 1 156215 234323 (by norm_num) (by norm_num) (sr 1 234323 351485 (by norm_num) (by norm_num) (sr 3 351485 131807 (by norm_num) (by norm_num) (sr 1 131807 197711 (by norm_num) (by norm_num) (sr 1 197711 296567 (by norm_num) (by norm_num) (sr 1 296567 444851 (by norm_num) (by norm_num) (sr 1 444851 667277 (by norm_num) (by norm_num) (sr 3 667277 250229 (by norm_num) (by norm_num) (sr 5 250229 23459 (by norm_num) (by norm_num) (B 23459 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R104147 : Reach 104147 := (sr 1 104147 156221 (by norm_num) (by norm_num) (sr 3 156221 58583 (by norm_num) (by norm_num) (B 58583 (by norm_num) (by norm_num) (by norm_num))))
theorem R104151 : Reach 104151 := (sr 1 104151 156227 (by norm_num) (by norm_num) (sr 1 156227 234341 (by norm_num) (by norm_num) (sr 4 234341 43939 (by norm_num) (by norm_num) (B 43939 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104155 : Reach 104155 := (sr 1 104155 156233 (by norm_num) (by norm_num) (sr 2 156233 117175 (by norm_num) (by norm_num) (sr 1 117175 175763 (by norm_num) (by norm_num) (sr 1 175763 263645 (by norm_num) (by norm_num) (sr 3 263645 98867 (by norm_num) (by norm_num) (B 98867 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104159 : Reach 104159 := (sr 1 104159 156239 (by norm_num) (by norm_num) (sr 1 156239 234359 (by norm_num) (by norm_num) (sr 1 234359 351539 (by norm_num) (by norm_num) (sr 1 351539 527309 (by norm_num) (by norm_num) (sr 3 527309 197741 (by norm_num) (by norm_num) (sr 3 197741 74153 (by norm_num) (by norm_num) (B 74153 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R104163 : Reach 104163 := (sr 1 104163 156245 (by norm_num) (by norm_num) (sr 8 156245 1831 (by norm_num) (by norm_num) (B 1831 (by norm_num) (by norm_num) (by norm_num))))
theorem R104167 : Reach 104167 := (sr 1 104167 156251 (by norm_num) (by norm_num) (sr 1 156251 234377 (by norm_num) (by norm_num) (sr 2 234377 175783 (by norm_num) (by norm_num) (sr 1 175783 263675 (by norm_num) (by norm_num) (sr 1 263675 395513 (by norm_num) (by norm_num) (sr 2 395513 296635 (by norm_num) (by norm_num) (sr 1 296635 444953 (by norm_num) (by norm_num) (sr 2 444953 333715 (by norm_num) (by norm_num) (sr 1 333715 500573 (by norm_num) (by norm_num) (sr 3 500573 187715 (by norm_num) (by norm_num) (sr 1 187715 281573 (by norm_num) (by norm_num) (sr 4 281573 52795 (by norm_num) (by norm_num) (B 52795 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R104171 : Reach 104171 := (sr 1 104171 156257 (by norm_num) (by norm_num) (sr 2 156257 117193 (by norm_num) (by norm_num) (sr 2 117193 87895 (by norm_num) (by norm_num) (B 87895 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104175 : Reach 104175 := (sr 1 104175 156263 (by norm_num) (by norm_num) (sr 1 156263 234395 (by norm_num) (by norm_num) (sr 1 234395 351593 (by norm_num) (by norm_num) (sr 2 351593 263695 (by norm_num) (by norm_num) (sr 1 263695 395543 (by norm_num) (by norm_num) (sr 1 395543 593315 (by norm_num) (by norm_num) (sr 1 593315 889973 (by norm_num) (by norm_num) (sr 5 889973 83435 (by norm_num) (by norm_num) (B 83435 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R104179 : Reach 104179 := (sr 1 104179 156269 (by norm_num) (by norm_num) (sr 3 156269 58601 (by norm_num) (by norm_num) (B 58601 (by norm_num) (by norm_num) (by norm_num))))
theorem R104183 : Reach 104183 := (sr 1 104183 156275 (by norm_num) (by norm_num) (sr 1 156275 234413 (by norm_num) (by norm_num) (sr 3 234413 87905 (by norm_num) (by norm_num) (B 87905 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104187 : Reach 104187 := (sr 1 104187 156281 (by norm_num) (by norm_num) (sr 2 156281 117211 (by norm_num) (by norm_num) (sr 1 117211 175817 (by norm_num) (by norm_num) (sr 2 175817 131863 (by norm_num) (by norm_num) (sr 1 131863 197795 (by norm_num) (by norm_num) (sr 1 197795 296693 (by norm_num) (by norm_num) (sr 5 296693 27815 (by norm_num) (by norm_num) (B 27815 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R104191 : Reach 104191 := (sr 1 104191 156287 (by norm_num) (by norm_num) (sr 1 156287 234431 (by norm_num) (by norm_num) (sr 1 234431 351647 (by norm_num) (by norm_num) (sr 1 351647 527471 (by norm_num) (by norm_num) (sr 1 527471 791207 (by norm_num) (by norm_num) (sr 1 791207 1186811 (by norm_num) (by norm_num) (sr 1 1186811 1780217 (by norm_num) (by norm_num) (sr 2 1780217 1335163 (by norm_num) (by norm_num) (sr 1 1335163 2002745 (by norm_num) (by norm_num) (sr 2 2002745 1502059 (by norm_num) (by norm_num) (sr 1 1502059 2253089 (by norm_num) (by norm_num) (sr 2 2253089 1689817 (by norm_num) (by norm_num) (sr 2 1689817 1267363 (by norm_num) (by norm_num) (sr 1 1267363 1901045 (by norm_num) (by norm_num) (sr 5 1901045 178223 (by norm_num) (by norm_num) (sr 1 178223 267335 (by norm_num) (by norm_num) (sr 1 267335 401003 (by norm_num) (by norm_num) (sr 1 401003 601505 (by norm_num) (by norm_num) (sr 2 601505 451129 (by norm_num) (by norm_num) (sr 2 451129 338347 (by norm_num) (by norm_num) (sr 1 338347 507521 (by norm_num) (by norm_num) (sr 2 507521 380641 (by norm_num) (by norm_num) (sr 2 380641 285481 (by norm_num) (by norm_num) (sr 2 285481 214111 (by norm_num) (by norm_num) (sr 1 214111 321167 (by norm_num) (by norm_num) (sr 1 321167 481751 (by norm_num) (by norm_num) (sr 1 481751 722627 (by norm_num) (by norm_num) (sr 1 722627 1083941 (by norm_num) (by norm_num) (sr 4 1083941 203239 (by norm_num) (by norm_num) (sr 1 203239 304859 (by norm_num) (by norm_num) (sr 1 304859 457289 (by norm_num) (by norm_num) (sr 2 457289 342967 (by norm_num) (by norm_num) (sr 1 342967 514451 (by norm_num) (by norm_num) (sr 1 514451 771677 (by norm_num) (by norm_num) (sr 3 771677 289379 (by norm_num) (by norm_num) (sr 1 289379 434069 (by norm_num) (by norm_num) (sr 6 434069 20347 (by norm_num) (by norm_num) (B 20347 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))))))))))
theorem R104195 : Reach 104195 := (sr 1 104195 156293 (by norm_num) (by norm_num) (sr 4 156293 29305 (by norm_num) (by norm_num) (B 29305 (by norm_num) (by norm_num) (by norm_num))))
theorem R104199 : Reach 104199 := (sr 1 104199 156299 (by norm_num) (by norm_num) (sr 1 156299 234449 (by norm_num) (by norm_num) (sr 2 234449 175837 (by norm_num) (by norm_num) (sr 3 175837 65939 (by norm_num) (by norm_num) (B 65939 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104203 : Reach 104203 := (sr 1 104203 156305 (by norm_num) (by norm_num) (sr 2 156305 117229 (by norm_num) (by norm_num) (sr 3 117229 43961 (by norm_num) (by norm_num) (B 43961 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104207 : Reach 104207 := (sr 1 104207 156311 (by norm_num) (by norm_num) (sr 1 156311 234467 (by norm_num) (by norm_num) (sr 1 234467 351701 (by norm_num) (by norm_num) (sr 7 351701 8243 (by norm_num) (by norm_num) (B 8243 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104211 : Reach 104211 := (sr 1 104211 156317 (by norm_num) (by norm_num) (sr 3 156317 58619 (by norm_num) (by norm_num) (B 58619 (by norm_num) (by norm_num) (by norm_num))))
theorem R104215 : Reach 104215 := (sr 1 104215 156323 (by norm_num) (by norm_num) (sr 1 156323 234485 (by norm_num) (by norm_num) (sr 5 234485 21983 (by norm_num) (by norm_num) (B 21983 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104219 : Reach 104219 := (sr 1 104219 156329 (by norm_num) (by norm_num) (sr 2 156329 117247 (by norm_num) (by norm_num) (sr 1 117247 175871 (by norm_num) (by norm_num) (sr 1 175871 263807 (by norm_num) (by norm_num) (sr 1 263807 395711 (by norm_num) (by norm_num) (sr 1 395711 593567 (by norm_num) (by norm_num) (sr 1 593567 890351 (by norm_num) (by norm_num) (sr 1 890351 1335527 (by norm_num) (by norm_num) (sr 1 1335527 2003291 (by norm_num) (by norm_num) (sr 1 2003291 3004937 (by norm_num) (by norm_num) (sr 2 3004937 2253703 (by norm_num) (by norm_num) (sr 1 2253703 3380555 (by norm_num) (by norm_num) (sr 1 3380555 5070833 (by norm_num) (by norm_num) (sr 2 5070833 3803125 (by norm_num) (by norm_num) (sr 5 3803125 356543 (by norm_num) (by norm_num) (sr 1 356543 534815 (by norm_num) (by norm_num) (sr 1 534815 802223 (by norm_num) (by norm_num) (sr 1 802223 1203335 (by norm_num) (by norm_num) (sr 1 1203335 1805003 (by norm_num) (by norm_num) (sr 1 1805003 2707505 (by norm_num) (by norm_num) (sr 2 2707505 2030629 (by norm_num) (by norm_num) (sr 4 2030629 380743 (by norm_num) (by norm_num) (sr 1 380743 571115 (by norm_num) (by norm_num) (sr 1 571115 856673 (by norm_num) (by norm_num) (sr 2 856673 642505 (by norm_num) (by norm_num) (sr 2 642505 481879 (by norm_num) (by norm_num) (sr 1 481879 722819 (by norm_num) (by norm_num) (sr 1 722819 1084229 (by norm_num) (by norm_num) (sr 4 1084229 203293 (by norm_num) (by norm_num) (sr 3 203293 76235 (by norm_num) (by norm_num) (B 76235 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))))
theorem R104223 : Reach 104223 := (sr 1 104223 156335 (by norm_num) (by norm_num) (sr 1 156335 234503 (by norm_num) (by norm_num) (sr 1 234503 351755 (by norm_num) (by norm_num) (sr 1 351755 527633 (by norm_num) (by norm_num) (sr 2 527633 395725 (by norm_num) (by norm_num) (sr 3 395725 148397 (by norm_num) (by norm_num) (sr 3 148397 55649 (by norm_num) (by norm_num) (B 55649 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R104227 : Reach 104227 := (sr 1 104227 156341 (by norm_num) (by norm_num) (sr 5 156341 14657 (by norm_num) (by norm_num) (B 14657 (by norm_num) (by norm_num) (by norm_num))))
theorem R104231 : Reach 104231 := (sr 1 104231 156347 (by norm_num) (by norm_num) (sr 1 156347 234521 (by norm_num) (by norm_num) (sr 2 234521 175891 (by norm_num) (by norm_num) (sr 1 175891 263837 (by norm_num) (by norm_num) (sr 3 263837 98939 (by norm_num) (by norm_num) (B 98939 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104235 : Reach 104235 := (sr 1 104235 156353 (by norm_num) (by norm_num) (sr 2 156353 117265 (by norm_num) (by norm_num) (sr 2 117265 87949 (by norm_num) (by norm_num) (B 87949 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104239 : Reach 104239 := (sr 1 104239 156359 (by norm_num) (by norm_num) (sr 1 156359 234539 (by norm_num) (by norm_num) (sr 1 234539 351809 (by norm_num) (by norm_num) (sr 2 351809 263857 (by norm_num) (by norm_num) (sr 2 263857 197893 (by norm_num) (by norm_num) (sr 4 197893 37105 (by norm_num) (by norm_num) (B 37105 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R104243 : Reach 104243 := (sr 1 104243 156365 (by norm_num) (by norm_num) (sr 3 156365 58637 (by norm_num) (by norm_num) (B 58637 (by norm_num) (by norm_num) (by norm_num))))
theorem R104247 : Reach 104247 := (sr 1 104247 156371 (by norm_num) (by norm_num) (sr 1 156371 234557 (by norm_num) (by norm_num) (sr 3 234557 87959 (by norm_num) (by norm_num) (B 87959 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104251 : Reach 104251 := (sr 1 104251 156377 (by norm_num) (by norm_num) (sr 2 156377 117283 (by norm_num) (by norm_num) (sr 1 117283 175925 (by norm_num) (by norm_num) (sr 5 175925 16493 (by norm_num) (by norm_num) (B 16493 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104255 : Reach 104255 := (sr 1 104255 156383 (by norm_num) (by norm_num) (sr 1 156383 234575 (by norm_num) (by norm_num) (sr 1 234575 351863 (by norm_num) (by norm_num) (sr 1 351863 527795 (by norm_num) (by norm_num) (sr 1 527795 791693 (by norm_num) (by norm_num) (sr 3 791693 296885 (by norm_num) (by norm_num) (sr 5 296885 27833 (by norm_num) (by norm_num) (B 27833 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R104259 : Reach 104259 := (sr 1 104259 156389 (by norm_num) (by norm_num) (sr 4 156389 29323 (by norm_num) (by norm_num) (B 29323 (by norm_num) (by norm_num) (by norm_num))))
theorem R104263 : Reach 104263 := (sr 1 104263 156395 (by norm_num) (by norm_num) (sr 1 156395 234593 (by norm_num) (by norm_num) (sr 2 234593 175945 (by norm_num) (by norm_num) (sr 2 175945 131959 (by norm_num) (by norm_num) (sr 1 131959 197939 (by norm_num) (by norm_num) (sr 1 197939 296909 (by norm_num) (by norm_num) (sr 3 296909 111341 (by norm_num) (by norm_num) (sr 3 111341 41753 (by norm_num) (by norm_num) (B 41753 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R104267 : Reach 104267 := (sr 1 104267 156401 (by norm_num) (by norm_num) (sr 2 156401 117301 (by norm_num) (by norm_num) (sr 5 117301 10997 (by norm_num) (by norm_num) (B 10997 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104271 : Reach 104271 := (sr 1 104271 156407 (by norm_num) (by norm_num) (sr 1 156407 234611 (by norm_num) (by norm_num) (sr 1 234611 351917 (by norm_num) (by norm_num) (sr 3 351917 131969 (by norm_num) (by norm_num) (sr 2 131969 98977 (by norm_num) (by norm_num) (B 98977 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104275 : Reach 104275 := (sr 1 104275 156413 (by norm_num) (by norm_num) (sr 3 156413 58655 (by norm_num) (by norm_num) (B 58655 (by norm_num) (by norm_num) (by norm_num))))
theorem R104279 : Reach 104279 := (sr 1 104279 156419 (by norm_num) (by norm_num) (sr 1 156419 234629 (by norm_num) (by norm_num) (sr 4 234629 43993 (by norm_num) (by norm_num) (B 43993 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104283 : Reach 104283 := (sr 1 104283 156425 (by norm_num) (by norm_num) (sr 2 156425 117319 (by norm_num) (by norm_num) (sr 1 117319 175979 (by norm_num) (by norm_num) (sr 1 175979 263969 (by norm_num) (by norm_num) (sr 2 263969 197977 (by norm_num) (by norm_num) (sr 2 197977 148483 (by norm_num) (by norm_num) (sr 1 148483 222725 (by norm_num) (by norm_num) (sr 4 222725 41761 (by norm_num) (by norm_num) (B 41761 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R104287 : Reach 104287 := (sr 1 104287 156431 (by norm_num) (by norm_num) (sr 1 156431 234647 (by norm_num) (by norm_num) (sr 1 234647 351971 (by norm_num) (by norm_num) (sr 1 351971 527957 (by norm_num) (by norm_num) (sr 8 527957 6187 (by norm_num) (by norm_num) (B 6187 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104291 : Reach 104291 := (sr 1 104291 156437 (by norm_num) (by norm_num) (sr 6 156437 7333 (by norm_num) (by norm_num) (B 7333 (by norm_num) (by norm_num) (by norm_num))))
theorem R104295 : Reach 104295 := (sr 1 104295 156443 (by norm_num) (by norm_num) (sr 1 156443 234665 (by norm_num) (by norm_num) (sr 2 234665 175999 (by norm_num) (by norm_num) (sr 1 175999 263999 (by norm_num) (by norm_num) (sr 1 263999 395999 (by norm_num) (by norm_num) (sr 1 395999 593999 (by norm_num) (by norm_num) (sr 1 593999 890999 (by norm_num) (by norm_num) (sr 1 890999 1336499 (by norm_num) (by norm_num) (sr 1 1336499 2004749 (by norm_num) (by norm_num) (sr 3 2004749 751781 (by norm_num) (by norm_num) (sr 4 751781 140959 (by norm_num) (by norm_num) (sr 1 140959 211439 (by norm_num) (by norm_num) (sr 1 211439 317159 (by norm_num) (by norm_num) (sr 1 317159 475739 (by norm_num) (by norm_num) (sr 1 475739 713609 (by norm_num) (by norm_num) (sr 2 713609 535207 (by norm_num) (by norm_num) (sr 1 535207 802811 (by norm_num) (by norm_num) (sr 1 802811 1204217 (by norm_num) (by norm_num) (sr 2 1204217 903163 (by norm_num) (by norm_num) (sr 1 903163 1354745 (by norm_num) (by norm_num) (sr 2 1354745 1016059 (by norm_num) (by norm_num) (sr 1 1016059 1524089 (by norm_num) (by norm_num) (sr 2 1524089 1143067 (by norm_num) (by norm_num) (sr 1 1143067 1714601 (by norm_num) (by norm_num) (sr 2 1714601 1285951 (by norm_num) (by norm_num) (sr 1 1285951 1928927 (by norm_num) (by norm_num) (sr 1 1928927 2893391 (by norm_num) (by norm_num) (sr 1 2893391 4340087 (by norm_num) (by norm_num) (sr 1 4340087 6510131 (by norm_num) (by norm_num) (sr 1 6510131 9765197 (by norm_num) (by norm_num) (sr 3 9765197 3661949 (by norm_num) (by norm_num) (sr 3 3661949 1373231 (by norm_num) (by norm_num) (sr 1 1373231 2059847 (by norm_num) (by norm_num) (sr 1 2059847 3089771 (by norm_num) (by norm_num) (sr 1 3089771 4634657 (by norm_num) (by norm_num) (sr 2 4634657 3475993 (by norm_num) (by norm_num) (sr 2 3475993 2606995 (by norm_num) (by norm_num) (sr 1 2606995 3910493 (by norm_num) (by norm_num) (sr 3 3910493 1466435 (by norm_num) (by norm_num) (sr 1 1466435 2199653 (by norm_num) (by norm_num) (sr 4 2199653 412435 (by norm_num) (by norm_num) (sr 1 412435 618653 (by norm_num) (by norm_num) (sr 3 618653 231995 (by norm_num) (by norm_num) (sr 1 231995 347993 (by norm_num) (by norm_num) (sr 2 347993 260995 (by norm_num) (by norm_num) (sr 1 260995 391493 (by norm_num) (by norm_num) (sr 4 391493 73405 (by norm_num) (by norm_num) (B 73405 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))))))))))))))))))))
theorem R104299 : Reach 104299 := (sr 1 104299 156449 (by norm_num) (by norm_num) (sr 2 156449 117337 (by norm_num) (by norm_num) (sr 2 117337 88003 (by norm_num) (by norm_num) (B 88003 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104303 : Reach 104303 := (sr 1 104303 156455 (by norm_num) (by norm_num) (sr 1 156455 234683 (by norm_num) (by norm_num) (sr 1 234683 352025 (by norm_num) (by norm_num) (sr 2 352025 264019 (by norm_num) (by norm_num) (sr 1 264019 396029 (by norm_num) (by norm_num) (sr 3 396029 148511 (by norm_num) (by norm_num) (sr 1 148511 222767 (by norm_num) (by norm_num) (sr 1 222767 334151 (by norm_num) (by norm_num) (sr 1 334151 501227 (by norm_num) (by norm_num) (sr 1 501227 751841 (by norm_num) (by norm_num) (sr 2 751841 563881 (by norm_num) (by norm_num) (sr 2 563881 422911 (by norm_num) (by norm_num) (sr 1 422911 634367 (by norm_num) (by norm_num) (sr 1 634367 951551 (by norm_num) (by norm_num) (sr 1 951551 1427327 (by norm_num) (by norm_num) (sr 1 1427327 2140991 (by norm_num) (by norm_num) (sr 1 2140991 3211487 (by norm_num) (by norm_num) (sr 1 3211487 4817231 (by norm_num) (by norm_num) (sr 1 4817231 7225847 (by norm_num) (by norm_num) (sr 1 7225847 10838771 (by norm_num) (by norm_num) (sr 1 10838771 16258157 (by norm_num) (by norm_num) (sr 3 16258157 6096809 (by norm_num) (by norm_num) (sr 2 6096809 4572607 (by norm_num) (by norm_num) (sr 1 4572607 6858911 (by norm_num) (by norm_num) (sr 1 6858911 10288367 (by norm_num) (by norm_num) (sr 1 10288367 15432551 (by norm_num) (by norm_num) (sr 1 15432551 23148827 (by norm_num) (by norm_num) (sr 1 23148827 34723241 (by norm_num) (by norm_num) (sr 2 34723241 26042431 (by norm_num) (by norm_num) (sr 1 26042431 39063647 (by norm_num) (by norm_num) (sr 1 39063647 58595471 (by norm_num) (by norm_num) (sr 1 58595471 87893207 (by norm_num) (by norm_num) (sr 1 87893207 131839811 (by norm_num) (by norm_num) (sr 1 131839811 197759717 (by norm_num) (by norm_num) (sr 4 197759717 37079947 (by norm_num) (by norm_num) (sr 1 37079947 55619921 (by norm_num) (by norm_num) (sr 2 55619921 41714941 (by norm_num) (by norm_num) (sr 3 41714941 15643103 (by norm_num) (by norm_num) (sr 1 15643103 23464655 (by norm_num) (by norm_num) (sr 1 23464655 35196983 (by norm_num) (by norm_num) (sr 1 35196983 52795475 (by norm_num) (by norm_num) (sr 1 52795475 79193213 (by norm_num) (by norm_num) (sr 3 79193213 29697455 (by norm_num) (by norm_num) (sr 1 29697455 44546183 (by norm_num) (by norm_num) (sr 1 44546183 66819275 (by norm_num) (by norm_num) (sr 1 66819275 100228913 (by norm_num) (by norm_num) (sr 2 100228913 75171685 (by norm_num) (by norm_num) (sr 4 75171685 14094691 (by norm_num) (by norm_num) (sr 1 14094691 21142037 (by norm_num) (by norm_num) (sr 6 21142037 991033 (by norm_num) (by norm_num) (sr 2 991033 743275 (by norm_num) (by norm_num) (sr 1 743275 1114913 (by norm_num) (by norm_num) (sr 2 1114913 836185 (by norm_num) (by norm_num) (sr 2 836185 627139 (by norm_num) (by norm_num) (sr 1 627139 940709 (by norm_num) (by norm_num) (sr 4 940709 176383 (by norm_num) (by norm_num) (sr 1 176383 264575 (by norm_num) (by norm_num) (sr 1 264575 396863 (by norm_num) (by norm_num) (sr 1 396863 595295 (by norm_num) (by norm_num) (sr 1 595295 892943 (by norm_num) (by norm_num) (sr 1 892943 1339415 (by norm_num) (by norm_num) (sr 1 1339415 2009123 (by norm_num) (by norm_num) (sr 1 2009123 3013685 (by norm_num) (by norm_num) (sr 5 3013685 282533 (by norm_num) (by norm_num) (sr 4 282533 52975 (by norm_num) (by norm_num) (B 52975 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem R104307 : Reach 104307 := (sr 1 104307 156461 (by norm_num) (by norm_num) (sr 3 156461 58673 (by norm_num) (by norm_num) (B 58673 (by norm_num) (by norm_num) (by norm_num))))
theorem R104311 : Reach 104311 := (sr 1 104311 156467 (by norm_num) (by norm_num) (sr 1 156467 234701 (by norm_num) (by norm_num) (sr 3 234701 88013 (by norm_num) (by norm_num) (B 88013 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104315 : Reach 104315 := (sr 1 104315 156473 (by norm_num) (by norm_num) (sr 2 156473 117355 (by norm_num) (by norm_num) (sr 1 117355 176033 (by norm_num) (by norm_num) (sr 2 176033 132025 (by norm_num) (by norm_num) (sr 2 132025 99019 (by norm_num) (by norm_num) (B 99019 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104319 : Reach 104319 := (sr 1 104319 156479 (by norm_num) (by norm_num) (sr 1 156479 234719 (by norm_num) (by norm_num) (sr 1 234719 352079 (by norm_num) (by norm_num) (sr 1 352079 528119 (by norm_num) (by norm_num) (sr 1 528119 792179 (by norm_num) (by norm_num) (sr 1 792179 1188269 (by norm_num) (by norm_num) (sr 3 1188269 445601 (by norm_num) (by norm_num) (sr 2 445601 334201 (by norm_num) (by norm_num) (sr 2 334201 250651 (by norm_num) (by norm_num) (sr 1 250651 375977 (by norm_num) (by norm_num) (sr 2 375977 281983 (by norm_num) (by norm_num) (sr 1 281983 422975 (by norm_num) (by norm_num) (sr 1 422975 634463 (by norm_num) (by norm_num) (sr 1 634463 951695 (by norm_num) (by norm_num) (sr 1 951695 1427543 (by norm_num) (by norm_num) (sr 1 1427543 2141315 (by norm_num) (by norm_num) (sr 1 2141315 3211973 (by norm_num) (by norm_num) (sr 4 3211973 602245 (by norm_num) (by norm_num) (sr 4 602245 112921 (by norm_num) (by norm_num) (sr 2 112921 84691 (by norm_num) (by norm_num) (B 84691 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))
theorem R104323 : Reach 104323 := (sr 1 104323 156485 (by norm_num) (by norm_num) (sr 4 156485 29341 (by norm_num) (by norm_num) (B 29341 (by norm_num) (by norm_num) (by norm_num))))
theorem R104327 : Reach 104327 := (sr 1 104327 156491 (by norm_num) (by norm_num) (sr 1 156491 234737 (by norm_num) (by norm_num) (sr 2 234737 176053 (by norm_num) (by norm_num) (sr 5 176053 16505 (by norm_num) (by norm_num) (B 16505 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104331 : Reach 104331 := (sr 1 104331 156497 (by norm_num) (by norm_num) (sr 2 156497 117373 (by norm_num) (by norm_num) (sr 3 117373 44015 (by norm_num) (by norm_num) (B 44015 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104335 : Reach 104335 := (sr 1 104335 156503 (by norm_num) (by norm_num) (sr 1 156503 234755 (by norm_num) (by norm_num) (sr 1 234755 352133 (by norm_num) (by norm_num) (sr 4 352133 66025 (by norm_num) (by norm_num) (B 66025 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104339 : Reach 104339 := (sr 1 104339 156509 (by norm_num) (by norm_num) (sr 3 156509 58691 (by norm_num) (by norm_num) (B 58691 (by norm_num) (by norm_num) (by norm_num))))
theorem R104343 : Reach 104343 := (sr 1 104343 156515 (by norm_num) (by norm_num) (sr 1 156515 234773 (by norm_num) (by norm_num) (sr 6 234773 11005 (by norm_num) (by norm_num) (B 11005 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104347 : Reach 104347 := (sr 1 104347 156521 (by norm_num) (by norm_num) (sr 2 156521 117391 (by norm_num) (by norm_num) (sr 1 117391 176087 (by norm_num) (by norm_num) (sr 1 176087 264131 (by norm_num) (by norm_num) (sr 1 264131 396197 (by norm_num) (by norm_num) (sr 4 396197 74287 (by norm_num) (by norm_num) (B 74287 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R104351 : Reach 104351 := (sr 1 104351 156527 (by norm_num) (by norm_num) (sr 1 156527 234791 (by norm_num) (by norm_num) (sr 1 234791 352187 (by norm_num) (by norm_num) (sr 1 352187 528281 (by norm_num) (by norm_num) (sr 2 528281 396211 (by norm_num) (by norm_num) (sr 1 396211 594317 (by norm_num) (by norm_num) (sr 3 594317 222869 (by norm_num) (by norm_num) (sr 6 222869 10447 (by norm_num) (by norm_num) (B 10447 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R104355 : Reach 104355 := (sr 1 104355 156533 (by norm_num) (by norm_num) (sr 5 156533 14675 (by norm_num) (by norm_num) (B 14675 (by norm_num) (by norm_num) (by norm_num))))
theorem R104359 : Reach 104359 := (sr 1 104359 156539 (by norm_num) (by norm_num) (sr 1 156539 234809 (by norm_num) (by norm_num) (sr 2 234809 176107 (by norm_num) (by norm_num) (sr 1 176107 264161 (by norm_num) (by norm_num) (sr 2 264161 198121 (by norm_num) (by norm_num) (sr 2 198121 148591 (by norm_num) (by norm_num) (sr 1 148591 222887 (by norm_num) (by norm_num) (sr 1 222887 334331 (by norm_num) (by norm_num) (sr 1 334331 501497 (by norm_num) (by norm_num) (sr 2 501497 376123 (by norm_num) (by norm_num) (sr 1 376123 564185 (by norm_num) (by norm_num) (sr 2 564185 423139 (by norm_num) (by norm_num) (sr 1 423139 634709 (by norm_num) (by norm_num) (sr 9 634709 3719 (by norm_num) (by norm_num) (B 3719 (by norm_num) (by norm_num) (by norm_num))))))))))))))))
theorem R104363 : Reach 104363 := (sr 1 104363 156545 (by norm_num) (by norm_num) (sr 2 156545 117409 (by norm_num) (by norm_num) (sr 2 117409 88057 (by norm_num) (by norm_num) (B 88057 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104367 : Reach 104367 := (sr 1 104367 156551 (by norm_num) (by norm_num) (sr 1 156551 234827 (by norm_num) (by norm_num) (sr 1 234827 352241 (by norm_num) (by norm_num) (sr 2 352241 264181 (by norm_num) (by norm_num) (sr 5 264181 24767 (by norm_num) (by norm_num) (B 24767 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104371 : Reach 104371 := (sr 1 104371 156557 (by norm_num) (by norm_num) (sr 3 156557 58709 (by norm_num) (by norm_num) (B 58709 (by norm_num) (by norm_num) (by norm_num))))
theorem R104375 : Reach 104375 := (sr 1 104375 156563 (by norm_num) (by norm_num) (sr 1 156563 234845 (by norm_num) (by norm_num) (sr 3 234845 88067 (by norm_num) (by norm_num) (B 88067 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104379 : Reach 104379 := (sr 1 104379 156569 (by norm_num) (by norm_num) (sr 2 156569 117427 (by norm_num) (by norm_num) (sr 1 117427 176141 (by norm_num) (by norm_num) (sr 3 176141 66053 (by norm_num) (by norm_num) (B 66053 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104383 : Reach 104383 := (sr 1 104383 156575 (by norm_num) (by norm_num) (sr 1 156575 234863 (by norm_num) (by norm_num) (sr 1 234863 352295 (by norm_num) (by norm_num) (sr 1 352295 528443 (by norm_num) (by norm_num) (sr 1 528443 792665 (by norm_num) (by norm_num) (sr 2 792665 594499 (by norm_num) (by norm_num) (sr 1 594499 891749 (by norm_num) (by norm_num) (sr 4 891749 167203 (by norm_num) (by norm_num) (sr 1 167203 250805 (by norm_num) (by norm_num) (sr 5 250805 23513 (by norm_num) (by norm_num) (B 23513 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R104387 : Reach 104387 := (sr 1 104387 156581 (by norm_num) (by norm_num) (sr 4 156581 29359 (by norm_num) (by norm_num) (B 29359 (by norm_num) (by norm_num) (by norm_num))))
theorem R104391 : Reach 104391 := (sr 1 104391 156587 (by norm_num) (by norm_num) (sr 1 156587 234881 (by norm_num) (by norm_num) (sr 2 234881 176161 (by norm_num) (by norm_num) (sr 2 176161 132121 (by norm_num) (by norm_num) (sr 2 132121 99091 (by norm_num) (by norm_num) (B 99091 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104395 : Reach 104395 := (sr 1 104395 156593 (by norm_num) (by norm_num) (sr 2 156593 117445 (by norm_num) (by norm_num) (sr 4 117445 22021 (by norm_num) (by norm_num) (B 22021 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104399 : Reach 104399 := (sr 1 104399 156599 (by norm_num) (by norm_num) (sr 1 156599 234899 (by norm_num) (by norm_num) (sr 1 234899 352349 (by norm_num) (by norm_num) (sr 3 352349 132131 (by norm_num) (by norm_num) (sr 1 132131 198197 (by norm_num) (by norm_num) (sr 5 198197 18581 (by norm_num) (by norm_num) (B 18581 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R104403 : Reach 104403 := (sr 1 104403 156605 (by norm_num) (by norm_num) (sr 3 156605 58727 (by norm_num) (by norm_num) (B 58727 (by norm_num) (by norm_num) (by norm_num))))
theorem R104407 : Reach 104407 := (sr 1 104407 156611 (by norm_num) (by norm_num) (sr 1 156611 234917 (by norm_num) (by norm_num) (sr 4 234917 44047 (by norm_num) (by norm_num) (B 44047 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104411 : Reach 104411 := (sr 1 104411 156617 (by norm_num) (by norm_num) (sr 2 156617 117463 (by norm_num) (by norm_num) (sr 1 117463 176195 (by norm_num) (by norm_num) (sr 1 176195 264293 (by norm_num) (by norm_num) (sr 4 264293 49555 (by norm_num) (by norm_num) (B 49555 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104415 : Reach 104415 := (sr 1 104415 156623 (by norm_num) (by norm_num) (sr 1 156623 234935 (by norm_num) (by norm_num) (sr 1 234935 352403 (by norm_num) (by norm_num) (sr 1 352403 528605 (by norm_num) (by norm_num) (sr 3 528605 198227 (by norm_num) (by norm_num) (sr 1 198227 297341 (by norm_num) (by norm_num) (sr 3 297341 111503 (by norm_num) (by norm_num) (sr 1 111503 167255 (by norm_num) (by norm_num) (sr 1 167255 250883 (by norm_num) (by norm_num) (sr 1 250883 376325 (by norm_num) (by norm_num) (sr 4 376325 70561 (by norm_num) (by norm_num) (B 70561 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R104419 : Reach 104419 := (sr 1 104419 156629 (by norm_num) (by norm_num) (sr 7 156629 3671 (by norm_num) (by norm_num) (B 3671 (by norm_num) (by norm_num) (by norm_num))))
theorem R104423 : Reach 104423 := (sr 1 104423 156635 (by norm_num) (by norm_num) (sr 1 156635 234953 (by norm_num) (by norm_num) (sr 2 234953 176215 (by norm_num) (by norm_num) (sr 1 176215 264323 (by norm_num) (by norm_num) (sr 1 264323 396485 (by norm_num) (by norm_num) (sr 4 396485 74341 (by norm_num) (by norm_num) (B 74341 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R104427 : Reach 104427 := (sr 1 104427 156641 (by norm_num) (by norm_num) (sr 2 156641 117481 (by norm_num) (by norm_num) (sr 2 117481 88111 (by norm_num) (by norm_num) (B 88111 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104431 : Reach 104431 := (sr 1 104431 156647 (by norm_num) (by norm_num) (sr 1 156647 234971 (by norm_num) (by norm_num) (sr 1 234971 352457 (by norm_num) (by norm_num) (sr 2 352457 264343 (by norm_num) (by norm_num) (sr 1 264343 396515 (by norm_num) (by norm_num) (sr 1 396515 594773 (by norm_num) (by norm_num) (sr 9 594773 3485 (by norm_num) (by norm_num) (B 3485 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R104435 : Reach 104435 := (sr 1 104435 156653 (by norm_num) (by norm_num) (sr 3 156653 58745 (by norm_num) (by norm_num) (B 58745 (by norm_num) (by norm_num) (by norm_num))))
theorem R104439 : Reach 104439 := (sr 1 104439 156659 (by norm_num) (by norm_num) (sr 1 156659 234989 (by norm_num) (by norm_num) (sr 3 234989 88121 (by norm_num) (by norm_num) (B 88121 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104443 : Reach 104443 := (sr 1 104443 156665 (by norm_num) (by norm_num) (sr 2 156665 117499 (by norm_num) (by norm_num) (sr 1 117499 176249 (by norm_num) (by norm_num) (sr 2 176249 132187 (by norm_num) (by norm_num) (sr 1 132187 198281 (by norm_num) (by norm_num) (sr 2 198281 148711 (by norm_num) (by norm_num) (sr 1 148711 223067 (by norm_num) (by norm_num) (sr 1 223067 334601 (by norm_num) (by norm_num) (sr 2 334601 250951 (by norm_num) (by norm_num) (sr 1 250951 376427 (by norm_num) (by norm_num) (sr 1 376427 564641 (by norm_num) (by norm_num) (sr 2 564641 423481 (by norm_num) (by norm_num) (sr 2 423481 317611 (by norm_num) (by norm_num) (sr 1 317611 476417 (by norm_num) (by norm_num) (sr 2 476417 357313 (by norm_num) (by norm_num) (sr 2 357313 267985 (by norm_num) (by norm_num) (sr 2 267985 200989 (by norm_num) (by norm_num) (sr 3 200989 75371 (by norm_num) (by norm_num) (B 75371 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))
theorem R104447 : Reach 104447 := (sr 1 104447 156671 (by norm_num) (by norm_num) (sr 1 156671 235007 (by norm_num) (by norm_num) (sr 1 235007 352511 (by norm_num) (by norm_num) (sr 1 352511 528767 (by norm_num) (by norm_num) (sr 1 528767 793151 (by norm_num) (by norm_num) (sr 1 793151 1189727 (by norm_num) (by norm_num) (sr 1 1189727 1784591 (by norm_num) (by norm_num) (sr 1 1784591 2676887 (by norm_num) (by norm_num) (sr 1 2676887 4015331 (by norm_num) (by norm_num) (sr 1 4015331 6022997 (by norm_num) (by norm_num) (sr 9 6022997 35291 (by norm_num) (by norm_num) (B 35291 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R104451 : Reach 104451 := (sr 1 104451 156677 (by norm_num) (by norm_num) (sr 4 156677 29377 (by norm_num) (by norm_num) (B 29377 (by norm_num) (by norm_num) (by norm_num))))
theorem R104455 : Reach 104455 := (sr 1 104455 156683 (by norm_num) (by norm_num) (sr 1 156683 235025 (by norm_num) (by norm_num) (sr 2 235025 176269 (by norm_num) (by norm_num) (sr 3 176269 66101 (by norm_num) (by norm_num) (B 66101 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104459 : Reach 104459 := (sr 1 104459 156689 (by norm_num) (by norm_num) (sr 2 156689 117517 (by norm_num) (by norm_num) (sr 3 117517 44069 (by norm_num) (by norm_num) (B 44069 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104463 : Reach 104463 := (sr 1 104463 156695 (by norm_num) (by norm_num) (sr 1 156695 235043 (by norm_num) (by norm_num) (sr 1 235043 352565 (by norm_num) (by norm_num) (sr 5 352565 33053 (by norm_num) (by norm_num) (B 33053 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104467 : Reach 104467 := (sr 1 104467 156701 (by norm_num) (by norm_num) (sr 3 156701 58763 (by norm_num) (by norm_num) (B 58763 (by norm_num) (by norm_num) (by norm_num))))
theorem R104471 : Reach 104471 := (sr 1 104471 156707 (by norm_num) (by norm_num) (sr 1 156707 235061 (by norm_num) (by norm_num) (sr 5 235061 22037 (by norm_num) (by norm_num) (B 22037 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104475 : Reach 104475 := (sr 1 104475 156713 (by norm_num) (by norm_num) (sr 2 156713 117535 (by norm_num) (by norm_num) (sr 1 117535 176303 (by norm_num) (by norm_num) (sr 1 176303 264455 (by norm_num) (by norm_num) (sr 1 264455 396683 (by norm_num) (by norm_num) (sr 1 396683 595025 (by norm_num) (by norm_num) (sr 2 595025 446269 (by norm_num) (by norm_num) (sr 3 446269 167351 (by norm_num) (by norm_num) (sr 1 167351 251027 (by norm_num) (by norm_num) (sr 1 251027 376541 (by norm_num) (by norm_num) (sr 3 376541 141203 (by norm_num) (by norm_num) (sr 1 141203 211805 (by norm_num) (by norm_num) (sr 3 211805 79427 (by norm_num) (by norm_num) (B 79427 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R104479 : Reach 104479 := (sr 1 104479 156719 (by norm_num) (by norm_num) (sr 1 156719 235079 (by norm_num) (by norm_num) (sr 1 235079 352619 (by norm_num) (by norm_num) (sr 1 352619 528929 (by norm_num) (by norm_num) (sr 2 528929 396697 (by norm_num) (by norm_num) (sr 2 396697 297523 (by norm_num) (by norm_num) (sr 1 297523 446285 (by norm_num) (by norm_num) (sr 3 446285 167357 (by norm_num) (by norm_num) (sr 3 167357 62759 (by norm_num) (by norm_num) (B 62759 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R104483 : Reach 104483 := (sr 1 104483 156725 (by norm_num) (by norm_num) (sr 5 156725 14693 (by norm_num) (by norm_num) (B 14693 (by norm_num) (by norm_num) (by norm_num))))
theorem R104487 : Reach 104487 := (sr 1 104487 156731 (by norm_num) (by norm_num) (sr 1 156731 235097 (by norm_num) (by norm_num) (sr 2 235097 176323 (by norm_num) (by norm_num) (sr 1 176323 264485 (by norm_num) (by norm_num) (sr 4 264485 49591 (by norm_num) (by norm_num) (B 49591 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104491 : Reach 104491 := (sr 1 104491 156737 (by norm_num) (by norm_num) (sr 2 156737 117553 (by norm_num) (by norm_num) (sr 2 117553 88165 (by norm_num) (by norm_num) (B 88165 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104495 : Reach 104495 := (sr 1 104495 156743 (by norm_num) (by norm_num) (sr 1 156743 235115 (by norm_num) (by norm_num) (sr 1 235115 352673 (by norm_num) (by norm_num) (sr 2 352673 264505 (by norm_num) (by norm_num) (sr 2 264505 198379 (by norm_num) (by norm_num) (sr 1 198379 297569 (by norm_num) (by norm_num) (sr 2 297569 223177 (by norm_num) (by norm_num) (sr 2 223177 167383 (by norm_num) (by norm_num) (sr 1 167383 251075 (by norm_num) (by norm_num) (sr 1 251075 376613 (by norm_num) (by norm_num) (sr 4 376613 70615 (by norm_num) (by norm_num) (B 70615 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R104499 : Reach 104499 := (sr 1 104499 156749 (by norm_num) (by norm_num) (sr 3 156749 58781 (by norm_num) (by norm_num) (B 58781 (by norm_num) (by norm_num) (by norm_num))))
theorem R104503 : Reach 104503 := (sr 1 104503 156755 (by norm_num) (by norm_num) (sr 1 156755 235133 (by norm_num) (by norm_num) (sr 3 235133 88175 (by norm_num) (by norm_num) (B 88175 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104507 : Reach 104507 := (sr 1 104507 156761 (by norm_num) (by norm_num) (sr 2 156761 117571 (by norm_num) (by norm_num) (sr 1 117571 176357 (by norm_num) (by norm_num) (sr 4 176357 33067 (by norm_num) (by norm_num) (B 33067 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104511 : Reach 104511 := (sr 1 104511 156767 (by norm_num) (by norm_num) (sr 1 156767 235151 (by norm_num) (by norm_num) (sr 1 235151 352727 (by norm_num) (by norm_num) (sr 1 352727 529091 (by norm_num) (by norm_num) (sr 1 529091 793637 (by norm_num) (by norm_num) (sr 4 793637 148807 (by norm_num) (by norm_num) (sr 1 148807 223211 (by norm_num) (by norm_num) (sr 1 223211 334817 (by norm_num) (by norm_num) (sr 2 334817 251113 (by norm_num) (by norm_num) (sr 2 251113 188335 (by norm_num) (by norm_num) (sr 1 188335 282503 (by norm_num) (by norm_num) (sr 1 282503 423755 (by norm_num) (by norm_num) (sr 1 423755 635633 (by norm_num) (by norm_num) (sr 2 635633 476725 (by norm_num) (by norm_num) (sr 5 476725 44693 (by norm_num) (by norm_num) (B 44693 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R104515 : Reach 104515 := (sr 1 104515 156773 (by norm_num) (by norm_num) (sr 4 156773 29395 (by norm_num) (by norm_num) (B 29395 (by norm_num) (by norm_num) (by norm_num))))
theorem R104519 : Reach 104519 := (sr 1 104519 156779 (by norm_num) (by norm_num) (sr 1 156779 235169 (by norm_num) (by norm_num) (sr 2 235169 176377 (by norm_num) (by norm_num) (sr 2 176377 132283 (by norm_num) (by norm_num) (sr 1 132283 198425 (by norm_num) (by norm_num) (sr 2 198425 148819 (by norm_num) (by norm_num) (sr 1 148819 223229 (by norm_num) (by norm_num) (sr 3 223229 83711 (by norm_num) (by norm_num) (B 83711 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R104523 : Reach 104523 := (sr 1 104523 156785 (by norm_num) (by norm_num) (sr 2 156785 117589 (by norm_num) (by norm_num) (sr 9 117589 689 (by norm_num) (by norm_num) (B 689 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104527 : Reach 104527 := (sr 1 104527 156791 (by norm_num) (by norm_num) (sr 1 156791 235187 (by norm_num) (by norm_num) (sr 1 235187 352781 (by norm_num) (by norm_num) (sr 3 352781 132293 (by norm_num) (by norm_num) (sr 4 132293 24805 (by norm_num) (by norm_num) (B 24805 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104531 : Reach 104531 := (sr 1 104531 156797 (by norm_num) (by norm_num) (sr 3 156797 58799 (by norm_num) (by norm_num) (B 58799 (by norm_num) (by norm_num) (by norm_num))))
theorem R104535 : Reach 104535 := (sr 1 104535 156803 (by norm_num) (by norm_num) (sr 1 156803 235205 (by norm_num) (by norm_num) (sr 4 235205 44101 (by norm_num) (by norm_num) (B 44101 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104539 : Reach 104539 := (sr 1 104539 156809 (by norm_num) (by norm_num) (sr 2 156809 117607 (by norm_num) (by norm_num) (sr 1 117607 176411 (by norm_num) (by norm_num) (sr 1 176411 264617 (by norm_num) (by norm_num) (sr 2 264617 198463 (by norm_num) (by norm_num) (sr 1 198463 297695 (by norm_num) (by norm_num) (sr 1 297695 446543 (by norm_num) (by norm_num) (sr 1 446543 669815 (by norm_num) (by norm_num) (sr 1 669815 1004723 (by norm_num) (by norm_num) (sr 1 1004723 1507085 (by norm_num) (by norm_num) (sr 3 1507085 565157 (by norm_num) (by norm_num) (sr 4 565157 105967 (by norm_num) (by norm_num) (sr 1 105967 158951 (by norm_num) (by norm_num) (sr 1 158951 238427 (by norm_num) (by norm_num) (sr 1 238427 357641 (by norm_num) (by norm_num) (sr 2 357641 268231 (by norm_num) (by norm_num) (sr 1 268231 402347 (by norm_num) (by norm_num) (sr 1 402347 603521 (by norm_num) (by norm_num) (sr 2 603521 452641 (by norm_num) (by norm_num) (sr 2 452641 339481 (by norm_num) (by norm_num) (sr 2 339481 254611 (by norm_num) (by norm_num) (sr 1 254611 381917 (by norm_num) (by norm_num) (sr 3 381917 143219 (by norm_num) (by norm_num) (sr 1 143219 214829 (by norm_num) (by norm_num) (sr 3 214829 80561 (by norm_num) (by norm_num) (B 80561 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))
theorem R104543 : Reach 104543 := (sr 1 104543 156815 (by norm_num) (by norm_num) (sr 1 156815 235223 (by norm_num) (by norm_num) (sr 1 235223 352835 (by norm_num) (by norm_num) (sr 1 352835 529253 (by norm_num) (by norm_num) (sr 4 529253 99235 (by norm_num) (by norm_num) (B 99235 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104547 : Reach 104547 := (sr 1 104547 156821 (by norm_num) (by norm_num) (sr 6 156821 7351 (by norm_num) (by norm_num) (B 7351 (by norm_num) (by norm_num) (by norm_num))))
theorem R104551 : Reach 104551 := (sr 1 104551 156827 (by norm_num) (by norm_num) (sr 1 156827 235241 (by norm_num) (by norm_num) (sr 2 235241 176431 (by norm_num) (by norm_num) (sr 1 176431 264647 (by norm_num) (by norm_num) (sr 1 264647 396971 (by norm_num) (by norm_num) (sr 1 396971 595457 (by norm_num) (by norm_num) (sr 2 595457 446593 (by norm_num) (by norm_num) (sr 2 446593 334945 (by norm_num) (by norm_num) (sr 2 334945 251209 (by norm_num) (by norm_num) (sr 2 251209 188407 (by norm_num) (by norm_num) (sr 1 188407 282611 (by norm_num) (by norm_num) (sr 1 282611 423917 (by norm_num) (by norm_num) (sr 3 423917 158969 (by norm_num) (by norm_num) (sr 2 158969 119227 (by norm_num) (by norm_num) (sr 1 119227 178841 (by norm_num) (by norm_num) (sr 2 178841 134131 (by norm_num) (by norm_num) (sr 1 134131 201197 (by norm_num) (by norm_num) (sr 3 201197 75449 (by norm_num) (by norm_num) (B 75449 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))
theorem R104555 : Reach 104555 := (sr 1 104555 156833 (by norm_num) (by norm_num) (sr 2 156833 117625 (by norm_num) (by norm_num) (sr 2 117625 88219 (by norm_num) (by norm_num) (B 88219 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104559 : Reach 104559 := (sr 1 104559 156839 (by norm_num) (by norm_num) (sr 1 156839 235259 (by norm_num) (by norm_num) (sr 1 235259 352889 (by norm_num) (by norm_num) (sr 2 352889 264667 (by norm_num) (by norm_num) (sr 1 264667 397001 (by norm_num) (by norm_num) (sr 2 397001 297751 (by norm_num) (by norm_num) (sr 1 297751 446627 (by norm_num) (by norm_num) (sr 1 446627 669941 (by norm_num) (by norm_num) (sr 5 669941 62807 (by norm_num) (by norm_num) (B 62807 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R104563 : Reach 104563 := (sr 1 104563 156845 (by norm_num) (by norm_num) (sr 3 156845 58817 (by norm_num) (by norm_num) (B 58817 (by norm_num) (by norm_num) (by norm_num))))
theorem R104567 : Reach 104567 := (sr 1 104567 156851 (by norm_num) (by norm_num) (sr 1 156851 235277 (by norm_num) (by norm_num) (sr 3 235277 88229 (by norm_num) (by norm_num) (B 88229 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104571 : Reach 104571 := (sr 1 104571 156857 (by norm_num) (by norm_num) (sr 2 156857 117643 (by norm_num) (by norm_num) (sr 1 117643 176465 (by norm_num) (by norm_num) (sr 2 176465 132349 (by norm_num) (by norm_num) (sr 3 132349 49631 (by norm_num) (by norm_num) (B 49631 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104575 : Reach 104575 := (sr 1 104575 156863 (by norm_num) (by norm_num) (sr 1 156863 235295 (by norm_num) (by norm_num) (sr 1 235295 352943 (by norm_num) (by norm_num) (sr 1 352943 529415 (by norm_num) (by norm_num) (sr 1 529415 794123 (by norm_num) (by norm_num) (sr 1 794123 1191185 (by norm_num) (by norm_num) (sr 2 1191185 893389 (by norm_num) (by norm_num) (sr 3 893389 335021 (by norm_num) (by norm_num) (sr 3 335021 125633 (by norm_num) (by norm_num) (sr 2 125633 94225 (by norm_num) (by norm_num) (B 94225 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R104579 : Reach 104579 := (sr 1 104579 156869 (by norm_num) (by norm_num) (sr 4 156869 29413 (by norm_num) (by norm_num) (B 29413 (by norm_num) (by norm_num) (by norm_num))))
theorem R104583 : Reach 104583 := (sr 1 104583 156875 (by norm_num) (by norm_num) (sr 1 156875 235313 (by norm_num) (by norm_num) (sr 2 235313 176485 (by norm_num) (by norm_num) (sr 4 176485 33091 (by norm_num) (by norm_num) (B 33091 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104587 : Reach 104587 := (sr 1 104587 156881 (by norm_num) (by norm_num) (sr 2 156881 117661 (by norm_num) (by norm_num) (sr 3 117661 44123 (by norm_num) (by norm_num) (B 44123 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104591 : Reach 104591 := (sr 1 104591 156887 (by norm_num) (by norm_num) (sr 1 156887 235331 (by norm_num) (by norm_num) (sr 1 235331 352997 (by norm_num) (by norm_num) (sr 4 352997 66187 (by norm_num) (by norm_num) (B 66187 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104595 : Reach 104595 := (sr 1 104595 156893 (by norm_num) (by norm_num) (sr 3 156893 58835 (by norm_num) (by norm_num) (B 58835 (by norm_num) (by norm_num) (by norm_num))))
theorem R104599 : Reach 104599 := (sr 1 104599 156899 (by norm_num) (by norm_num) (sr 1 156899 235349 (by norm_num) (by norm_num) (sr 9 235349 1379 (by norm_num) (by norm_num) (B 1379 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104603 : Reach 104603 := (sr 1 104603 156905 (by norm_num) (by norm_num) (sr 2 156905 117679 (by norm_num) (by norm_num) (sr 1 117679 176519 (by norm_num) (by norm_num) (sr 1 176519 264779 (by norm_num) (by norm_num) (sr 1 264779 397169 (by norm_num) (by norm_num) (sr 2 397169 297877 (by norm_num) (by norm_num) (sr 6 297877 13963 (by norm_num) (by norm_num) (B 13963 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R104607 : Reach 104607 := (sr 1 104607 156911 (by norm_num) (by norm_num) (sr 1 156911 235367 (by norm_num) (by norm_num) (sr 1 235367 353051 (by norm_num) (by norm_num) (sr 1 353051 529577 (by norm_num) (by norm_num) (sr 2 529577 397183 (by norm_num) (by norm_num) (sr 1 397183 595775 (by norm_num) (by norm_num) (sr 1 595775 893663 (by norm_num) (by norm_num) (sr 1 893663 1340495 (by norm_num) (by norm_num) (sr 1 1340495 2010743 (by norm_num) (by norm_num) (sr 1 2010743 3016115 (by norm_num) (by norm_num) (sr 1 3016115 4524173 (by norm_num) (by norm_num) (sr 3 4524173 1696565 (by norm_num) (by norm_num) (sr 5 1696565 159053 (by norm_num) (by norm_num) (sr 3 159053 59645 (by norm_num) (by norm_num) (B 59645 (by norm_num) (by norm_num) (by norm_num))))))))))))))))
theorem R104611 : Reach 104611 := (sr 1 104611 156917 (by norm_num) (by norm_num) (sr 5 156917 14711 (by norm_num) (by norm_num) (B 14711 (by norm_num) (by norm_num) (by norm_num))))
theorem R104615 : Reach 104615 := (sr 1 104615 156923 (by norm_num) (by norm_num) (sr 1 156923 235385 (by norm_num) (by norm_num) (sr 2 235385 176539 (by norm_num) (by norm_num) (sr 1 176539 264809 (by norm_num) (by norm_num) (sr 2 264809 198607 (by norm_num) (by norm_num) (sr 1 198607 297911 (by norm_num) (by norm_num) (sr 1 297911 446867 (by norm_num) (by norm_num) (sr 1 446867 670301 (by norm_num) (by norm_num) (sr 3 670301 251363 (by norm_num) (by norm_num) (sr 1 251363 377045 (by norm_num) (by norm_num) (sr 7 377045 8837 (by norm_num) (by norm_num) (B 8837 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R104619 : Reach 104619 := (sr 1 104619 156929 (by norm_num) (by norm_num) (sr 2 156929 117697 (by norm_num) (by norm_num) (sr 2 117697 88273 (by norm_num) (by norm_num) (B 88273 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104623 : Reach 104623 := (sr 1 104623 156935 (by norm_num) (by norm_num) (sr 1 156935 235403 (by norm_num) (by norm_num) (sr 1 235403 353105 (by norm_num) (by norm_num) (sr 2 353105 264829 (by norm_num) (by norm_num) (sr 3 264829 99311 (by norm_num) (by norm_num) (B 99311 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104627 : Reach 104627 := (sr 1 104627 156941 (by norm_num) (by norm_num) (sr 3 156941 58853 (by norm_num) (by norm_num) (B 58853 (by norm_num) (by norm_num) (by norm_num))))
theorem R104631 : Reach 104631 := (sr 1 104631 156947 (by norm_num) (by norm_num) (sr 1 156947 235421 (by norm_num) (by norm_num) (sr 3 235421 88283 (by norm_num) (by norm_num) (B 88283 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104635 : Reach 104635 := (sr 1 104635 156953 (by norm_num) (by norm_num) (sr 2 156953 117715 (by norm_num) (by norm_num) (sr 1 117715 176573 (by norm_num) (by norm_num) (sr 3 176573 66215 (by norm_num) (by norm_num) (B 66215 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104639 : Reach 104639 := (sr 1 104639 156959 (by norm_num) (by norm_num) (sr 1 156959 235439 (by norm_num) (by norm_num) (sr 1 235439 353159 (by norm_num) (by norm_num) (sr 1 353159 529739 (by norm_num) (by norm_num) (sr 1 529739 794609 (by norm_num) (by norm_num) (sr 2 794609 595957 (by norm_num) (by norm_num) (sr 5 595957 55871 (by norm_num) (by norm_num) (B 55871 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R104643 : Reach 104643 := (sr 1 104643 156965 (by norm_num) (by norm_num) (sr 4 156965 29431 (by norm_num) (by norm_num) (B 29431 (by norm_num) (by norm_num) (by norm_num))))
theorem R104647 : Reach 104647 := (sr 1 104647 156971 (by norm_num) (by norm_num) (sr 1 156971 235457 (by norm_num) (by norm_num) (sr 2 235457 176593 (by norm_num) (by norm_num) (sr 2 176593 132445 (by norm_num) (by norm_num) (sr 3 132445 49667 (by norm_num) (by norm_num) (B 49667 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104651 : Reach 104651 := (sr 1 104651 156977 (by norm_num) (by norm_num) (sr 2 156977 117733 (by norm_num) (by norm_num) (sr 4 117733 22075 (by norm_num) (by norm_num) (B 22075 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104655 : Reach 104655 := (sr 1 104655 156983 (by norm_num) (by norm_num) (sr 1 156983 235475 (by norm_num) (by norm_num) (sr 1 235475 353213 (by norm_num) (by norm_num) (sr 3 353213 132455 (by norm_num) (by norm_num) (sr 1 132455 198683 (by norm_num) (by norm_num) (sr 1 198683 298025 (by norm_num) (by norm_num) (sr 2 298025 223519 (by norm_num) (by norm_num) (sr 1 223519 335279 (by norm_num) (by norm_num) (sr 1 335279 502919 (by norm_num) (by norm_num) (sr 1 502919 754379 (by norm_num) (by norm_num) (sr 1 754379 1131569 (by norm_num) (by norm_num) (sr 2 1131569 848677 (by norm_num) (by norm_num) (sr 4 848677 159127 (by norm_num) (by norm_num) (sr 1 159127 238691 (by norm_num) (by norm_num) (sr 1 238691 358037 (by norm_num) (by norm_num) (sr 6 358037 16783 (by norm_num) (by norm_num) (B 16783 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))
theorem R104659 : Reach 104659 := (sr 1 104659 156989 (by norm_num) (by norm_num) (sr 3 156989 58871 (by norm_num) (by norm_num) (B 58871 (by norm_num) (by norm_num) (by norm_num))))
theorem R104663 : Reach 104663 := (sr 1 104663 156995 (by norm_num) (by norm_num) (sr 1 156995 235493 (by norm_num) (by norm_num) (sr 4 235493 44155 (by norm_num) (by norm_num) (B 44155 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104667 : Reach 104667 := (sr 1 104667 157001 (by norm_num) (by norm_num) (sr 2 157001 117751 (by norm_num) (by norm_num) (sr 1 117751 176627 (by norm_num) (by norm_num) (sr 1 176627 264941 (by norm_num) (by norm_num) (sr 3 264941 99353 (by norm_num) (by norm_num) (B 99353 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104671 : Reach 104671 := (sr 1 104671 157007 (by norm_num) (by norm_num) (sr 1 157007 235511 (by norm_num) (by norm_num) (sr 1 235511 353267 (by norm_num) (by norm_num) (sr 1 353267 529901 (by norm_num) (by norm_num) (sr 3 529901 198713 (by norm_num) (by norm_num) (sr 2 198713 149035 (by norm_num) (by norm_num) (sr 1 149035 223553 (by norm_num) (by norm_num) (sr 2 223553 167665 (by norm_num) (by norm_num) (sr 2 167665 125749 (by norm_num) (by norm_num) (sr 5 125749 11789 (by norm_num) (by norm_num) (B 11789 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R104675 : Reach 104675 := (sr 1 104675 157013 (by norm_num) (by norm_num) (sr 12 157013 115 (by norm_num) (by norm_num) (B 115 (by norm_num) (by norm_num) (by norm_num))))
theorem R104679 : Reach 104679 := (sr 1 104679 157019 (by norm_num) (by norm_num) (sr 1 157019 235529 (by norm_num) (by norm_num) (sr 2 235529 176647 (by norm_num) (by norm_num) (sr 1 176647 264971 (by norm_num) (by norm_num) (sr 1 264971 397457 (by norm_num) (by norm_num) (sr 2 397457 298093 (by norm_num) (by norm_num) (sr 3 298093 111785 (by norm_num) (by norm_num) (sr 2 111785 83839 (by norm_num) (by norm_num) (B 83839 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R104683 : Reach 104683 := (sr 1 104683 157025 (by norm_num) (by norm_num) (sr 2 157025 117769 (by norm_num) (by norm_num) (sr 2 117769 88327 (by norm_num) (by norm_num) (B 88327 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104687 : Reach 104687 := (sr 1 104687 157031 (by norm_num) (by norm_num) (sr 1 157031 235547 (by norm_num) (by norm_num) (sr 1 235547 353321 (by norm_num) (by norm_num) (sr 2 353321 264991 (by norm_num) (by norm_num) (sr 1 264991 397487 (by norm_num) (by norm_num) (sr 1 397487 596231 (by norm_num) (by norm_num) (sr 1 596231 894347 (by norm_num) (by norm_num) (sr 1 894347 1341521 (by norm_num) (by norm_num) (sr 2 1341521 1006141 (by norm_num) (by norm_num) (sr 3 1006141 377303 (by norm_num) (by norm_num) (sr 1 377303 565955 (by norm_num) (by norm_num) (sr 1 565955 848933 (by norm_num) (by norm_num) (sr 4 848933 159175 (by norm_num) (by norm_num) (sr 1 159175 238763 (by norm_num) (by norm_num) (sr 1 238763 358145 (by norm_num) (by norm_num) (sr 2 358145 268609 (by norm_num) (by norm_num) (sr 2 268609 201457 (by norm_num) (by norm_num) (sr 2 201457 151093 (by norm_num) (by norm_num) (sr 5 151093 14165 (by norm_num) (by norm_num) (B 14165 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))
theorem R104691 : Reach 104691 := (sr 1 104691 157037 (by norm_num) (by norm_num) (sr 3 157037 58889 (by norm_num) (by norm_num) (B 58889 (by norm_num) (by norm_num) (by norm_num))))
theorem R104695 : Reach 104695 := (sr 1 104695 157043 (by norm_num) (by norm_num) (sr 1 157043 235565 (by norm_num) (by norm_num) (sr 3 235565 88337 (by norm_num) (by norm_num) (B 88337 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104699 : Reach 104699 := (sr 1 104699 157049 (by norm_num) (by norm_num) (sr 2 157049 117787 (by norm_num) (by norm_num) (sr 1 117787 176681 (by norm_num) (by norm_num) (sr 2 176681 132511 (by norm_num) (by norm_num) (sr 1 132511 198767 (by norm_num) (by norm_num) (sr 1 198767 298151 (by norm_num) (by norm_num) (sr 1 298151 447227 (by norm_num) (by norm_num) (sr 1 447227 670841 (by norm_num) (by norm_num) (sr 2 670841 503131 (by norm_num) (by norm_num) (sr 1 503131 754697 (by norm_num) (by norm_num) (sr 2 754697 566023 (by norm_num) (by norm_num) (sr 1 566023 849035 (by norm_num) (by norm_num) (sr 1 849035 1273553 (by norm_num) (by norm_num) (sr 2 1273553 955165 (by norm_num) (by norm_num) (sr 3 955165 358187 (by norm_num) (by norm_num) (sr 1 358187 537281 (by norm_num) (by norm_num) (sr 2 537281 402961 (by norm_num) (by norm_num) (sr 2 402961 302221 (by norm_num) (by norm_num) (sr 3 302221 113333 (by norm_num) (by norm_num) (sr 5 113333 10625 (by norm_num) (by norm_num) (B 10625 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))
theorem R104703 : Reach 104703 := (sr 1 104703 157055 (by norm_num) (by norm_num) (sr 1 157055 235583 (by norm_num) (by norm_num) (sr 1 235583 353375 (by norm_num) (by norm_num) (sr 1 353375 530063 (by norm_num) (by norm_num) (sr 1 530063 795095 (by norm_num) (by norm_num) (sr 1 795095 1192643 (by norm_num) (by norm_num) (sr 1 1192643 1788965 (by norm_num) (by norm_num) (sr 4 1788965 335431 (by norm_num) (by norm_num) (sr 1 335431 503147 (by norm_num) (by norm_num) (sr 1 503147 754721 (by norm_num) (by norm_num) (sr 2 754721 566041 (by norm_num) (by norm_num) (sr 2 566041 424531 (by norm_num) (by norm_num) (sr 1 424531 636797 (by norm_num) (by norm_num) (sr 3 636797 238799 (by norm_num) (by norm_num) (sr 1 238799 358199 (by norm_num) (by norm_num) (sr 1 358199 537299 (by norm_num) (by norm_num) (sr 1 537299 805949 (by norm_num) (by norm_num) (sr 3 805949 302231 (by norm_num) (by norm_num) (sr 1 302231 453347 (by norm_num) (by norm_num) (sr 1 453347 680021 (by norm_num) (by norm_num) (sr 8 680021 7969 (by norm_num) (by norm_num) (B 7969 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))
theorem R104707 : Reach 104707 := (sr 1 104707 157061 (by norm_num) (by norm_num) (sr 4 157061 29449 (by norm_num) (by norm_num) (B 29449 (by norm_num) (by norm_num) (by norm_num))))
theorem R104711 : Reach 104711 := (sr 1 104711 157067 (by norm_num) (by norm_num) (sr 1 157067 235601 (by norm_num) (by norm_num) (sr 2 235601 176701 (by norm_num) (by norm_num) (sr 3 176701 66263 (by norm_num) (by norm_num) (B 66263 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104715 : Reach 104715 := (sr 1 104715 157073 (by norm_num) (by norm_num) (sr 2 157073 117805 (by norm_num) (by norm_num) (sr 3 117805 44177 (by norm_num) (by norm_num) (B 44177 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104719 : Reach 104719 := (sr 1 104719 157079 (by norm_num) (by norm_num) (sr 1 157079 235619 (by norm_num) (by norm_num) (sr 1 235619 353429 (by norm_num) (by norm_num) (sr 6 353429 16567 (by norm_num) (by norm_num) (B 16567 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104723 : Reach 104723 := (sr 1 104723 157085 (by norm_num) (by norm_num) (sr 3 157085 58907 (by norm_num) (by norm_num) (B 58907 (by norm_num) (by norm_num) (by norm_num))))
theorem R104727 : Reach 104727 := (sr 1 104727 157091 (by norm_num) (by norm_num) (sr 1 157091 235637 (by norm_num) (by norm_num) (sr 5 235637 22091 (by norm_num) (by norm_num) (B 22091 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104731 : Reach 104731 := (sr 1 104731 157097 (by norm_num) (by norm_num) (sr 2 157097 117823 (by norm_num) (by norm_num) (sr 1 117823 176735 (by norm_num) (by norm_num) (sr 1 176735 265103 (by norm_num) (by norm_num) (sr 1 265103 397655 (by norm_num) (by norm_num) (sr 1 397655 596483 (by norm_num) (by norm_num) (sr 1 596483 894725 (by norm_num) (by norm_num) (sr 4 894725 167761 (by norm_num) (by norm_num) (sr 2 167761 125821 (by norm_num) (by norm_num) (sr 3 125821 47183 (by norm_num) (by norm_num) (B 47183 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R104735 : Reach 104735 := (sr 1 104735 157103 (by norm_num) (by norm_num) (sr 1 157103 235655 (by norm_num) (by norm_num) (sr 1 235655 353483 (by norm_num) (by norm_num) (sr 1 353483 530225 (by norm_num) (by norm_num) (sr 2 530225 397669 (by norm_num) (by norm_num) (sr 4 397669 74563 (by norm_num) (by norm_num) (B 74563 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R104739 : Reach 104739 := (sr 1 104739 157109 (by norm_num) (by norm_num) (sr 5 157109 14729 (by norm_num) (by norm_num) (B 14729 (by norm_num) (by norm_num) (by norm_num))))
theorem R104743 : Reach 104743 := (sr 1 104743 157115 (by norm_num) (by norm_num) (sr 1 157115 235673 (by norm_num) (by norm_num) (sr 2 235673 176755 (by norm_num) (by norm_num) (sr 1 176755 265133 (by norm_num) (by norm_num) (sr 3 265133 99425 (by norm_num) (by norm_num) (B 99425 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104747 : Reach 104747 := (sr 1 104747 157121 (by norm_num) (by norm_num) (sr 2 157121 117841 (by norm_num) (by norm_num) (sr 2 117841 88381 (by norm_num) (by norm_num) (B 88381 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104751 : Reach 104751 := (sr 1 104751 157127 (by norm_num) (by norm_num) (sr 1 157127 235691 (by norm_num) (by norm_num) (sr 1 235691 353537 (by norm_num) (by norm_num) (sr 2 353537 265153 (by norm_num) (by norm_num) (sr 2 265153 198865 (by norm_num) (by norm_num) (sr 2 198865 149149 (by norm_num) (by norm_num) (sr 3 149149 55931 (by norm_num) (by norm_num) (B 55931 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R104755 : Reach 104755 := (sr 1 104755 157133 (by norm_num) (by norm_num) (sr 3 157133 58925 (by norm_num) (by norm_num) (B 58925 (by norm_num) (by norm_num) (by norm_num))))
theorem R104759 : Reach 104759 := (sr 1 104759 157139 (by norm_num) (by norm_num) (sr 1 157139 235709 (by norm_num) (by norm_num) (sr 3 235709 88391 (by norm_num) (by norm_num) (B 88391 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104763 : Reach 104763 := (sr 1 104763 157145 (by norm_num) (by norm_num) (sr 2 157145 117859 (by norm_num) (by norm_num) (sr 1 117859 176789 (by norm_num) (by norm_num) (sr 6 176789 8287 (by norm_num) (by norm_num) (B 8287 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104767 : Reach 104767 := (sr 1 104767 157151 (by norm_num) (by norm_num) (sr 1 157151 235727 (by norm_num) (by norm_num) (sr 1 235727 353591 (by norm_num) (by norm_num) (sr 1 353591 530387 (by norm_num) (by norm_num) (sr 1 530387 795581 (by norm_num) (by norm_num) (sr 3 795581 298343 (by norm_num) (by norm_num) (sr 1 298343 447515 (by norm_num) (by norm_num) (sr 1 447515 671273 (by norm_num) (by norm_num) (sr 2 671273 503455 (by norm_num) (by norm_num) (sr 1 503455 755183 (by norm_num) (by norm_num) (sr 1 755183 1132775 (by norm_num) (by norm_num) (sr 1 1132775 1699163 (by norm_num) (by norm_num) (sr 1 1699163 2548745 (by norm_num) (by norm_num) (sr 2 2548745 1911559 (by norm_num) (by norm_num) (sr 1 1911559 2867339 (by norm_num) (by norm_num) (sr 1 2867339 4301009 (by norm_num) (by norm_num) (sr 2 4301009 3225757 (by norm_num) (by norm_num) (sr 3 3225757 1209659 (by norm_num) (by norm_num) (sr 1 1209659 1814489 (by norm_num) (by norm_num) (sr 2 1814489 1360867 (by norm_num) (by norm_num) (sr 1 1360867 2041301 (by norm_num) (by norm_num) (sr 7 2041301 47843 (by norm_num) (by norm_num) (B 47843 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R104771 : Reach 104771 := (sr 1 104771 157157 (by norm_num) (by norm_num) (sr 4 157157 29467 (by norm_num) (by norm_num) (B 29467 (by norm_num) (by norm_num) (by norm_num))))
theorem R104775 : Reach 104775 := (sr 1 104775 157163 (by norm_num) (by norm_num) (sr 1 157163 235745 (by norm_num) (by norm_num) (sr 2 235745 176809 (by norm_num) (by norm_num) (sr 2 176809 132607 (by norm_num) (by norm_num) (sr 1 132607 198911 (by norm_num) (by norm_num) (sr 1 198911 298367 (by norm_num) (by norm_num) (sr 1 298367 447551 (by norm_num) (by norm_num) (sr 1 447551 671327 (by norm_num) (by norm_num) (sr 1 671327 1006991 (by norm_num) (by norm_num) (sr 1 1006991 1510487 (by norm_num) (by norm_num) (sr 1 1510487 2265731 (by norm_num) (by norm_num) (sr 1 2265731 3398597 (by norm_num) (by norm_num) (sr 4 3398597 637237 (by norm_num) (by norm_num) (sr 5 637237 59741 (by norm_num) (by norm_num) (B 59741 (by norm_num) (by norm_num) (by norm_num))))))))))))))))
theorem R104779 : Reach 104779 := (sr 1 104779 157169 (by norm_num) (by norm_num) (sr 2 157169 117877 (by norm_num) (by norm_num) (sr 5 117877 11051 (by norm_num) (by norm_num) (B 11051 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104783 : Reach 104783 := (sr 1 104783 157175 (by norm_num) (by norm_num) (sr 1 157175 235763 (by norm_num) (by norm_num) (sr 1 235763 353645 (by norm_num) (by norm_num) (sr 3 353645 132617 (by norm_num) (by norm_num) (sr 2 132617 99463 (by norm_num) (by norm_num) (B 99463 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104787 : Reach 104787 := (sr 1 104787 157181 (by norm_num) (by norm_num) (sr 3 157181 58943 (by norm_num) (by norm_num) (B 58943 (by norm_num) (by norm_num) (by norm_num))))
theorem R104791 : Reach 104791 := (sr 1 104791 157187 (by norm_num) (by norm_num) (sr 1 157187 235781 (by norm_num) (by norm_num) (sr 4 235781 44209 (by norm_num) (by norm_num) (B 44209 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104795 : Reach 104795 := (sr 1 104795 157193 (by norm_num) (by norm_num) (sr 2 157193 117895 (by norm_num) (by norm_num) (sr 1 117895 176843 (by norm_num) (by norm_num) (sr 1 176843 265265 (by norm_num) (by norm_num) (sr 2 265265 198949 (by norm_num) (by norm_num) (sr 4 198949 37303 (by norm_num) (by norm_num) (B 37303 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R104799 : Reach 104799 := (sr 1 104799 157199 (by norm_num) (by norm_num) (sr 1 157199 235799 (by norm_num) (by norm_num) (sr 1 235799 353699 (by norm_num) (by norm_num) (sr 1 353699 530549 (by norm_num) (by norm_num) (sr 5 530549 49739 (by norm_num) (by norm_num) (B 49739 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104803 : Reach 104803 := (sr 1 104803 157205 (by norm_num) (by norm_num) (sr 6 157205 7369 (by norm_num) (by norm_num) (B 7369 (by norm_num) (by norm_num) (by norm_num))))
theorem R104807 : Reach 104807 := (sr 1 104807 157211 (by norm_num) (by norm_num) (sr 1 157211 235817 (by norm_num) (by norm_num) (sr 2 235817 176863 (by norm_num) (by norm_num) (sr 1 176863 265295 (by norm_num) (by norm_num) (sr 1 265295 397943 (by norm_num) (by norm_num) (sr 1 397943 596915 (by norm_num) (by norm_num) (sr 1 596915 895373 (by norm_num) (by norm_num) (sr 3 895373 335765 (by norm_num) (by norm_num) (sr 6 335765 15739 (by norm_num) (by norm_num) (B 15739 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R104811 : Reach 104811 := (sr 1 104811 157217 (by norm_num) (by norm_num) (sr 2 157217 117913 (by norm_num) (by norm_num) (sr 2 117913 88435 (by norm_num) (by norm_num) (B 88435 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104815 : Reach 104815 := (sr 1 104815 157223 (by norm_num) (by norm_num) (sr 1 157223 235835 (by norm_num) (by norm_num) (sr 1 235835 353753 (by norm_num) (by norm_num) (sr 2 353753 265315 (by norm_num) (by norm_num) (sr 1 265315 397973 (by norm_num) (by norm_num) (sr 6 397973 18655 (by norm_num) (by norm_num) (B 18655 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R104819 : Reach 104819 := (sr 1 104819 157229 (by norm_num) (by norm_num) (sr 3 157229 58961 (by norm_num) (by norm_num) (B 58961 (by norm_num) (by norm_num) (by norm_num))))
theorem R104823 : Reach 104823 := (sr 1 104823 157235 (by norm_num) (by norm_num) (sr 1 157235 235853 (by norm_num) (by norm_num) (sr 3 235853 88445 (by norm_num) (by norm_num) (B 88445 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104827 : Reach 104827 := (sr 1 104827 157241 (by norm_num) (by norm_num) (sr 2 157241 117931 (by norm_num) (by norm_num) (sr 1 117931 176897 (by norm_num) (by norm_num) (sr 2 176897 132673 (by norm_num) (by norm_num) (sr 2 132673 99505 (by norm_num) (by norm_num) (B 99505 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104831 : Reach 104831 := (sr 1 104831 157247 (by norm_num) (by norm_num) (sr 1 157247 235871 (by norm_num) (by norm_num) (sr 1 235871 353807 (by norm_num) (by norm_num) (sr 1 353807 530711 (by norm_num) (by norm_num) (sr 1 530711 796067 (by norm_num) (by norm_num) (sr 1 796067 1194101 (by norm_num) (by norm_num) (sr 5 1194101 111947 (by norm_num) (by norm_num) (sr 1 111947 167921 (by norm_num) (by norm_num) (sr 2 167921 125941 (by norm_num) (by norm_num) (sr 5 125941 11807 (by norm_num) (by norm_num) (B 11807 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R104835 : Reach 104835 := (sr 1 104835 157253 (by norm_num) (by norm_num) (sr 4 157253 29485 (by norm_num) (by norm_num) (B 29485 (by norm_num) (by norm_num) (by norm_num))))
theorem R104839 : Reach 104839 := (sr 1 104839 157259 (by norm_num) (by norm_num) (sr 1 157259 235889 (by norm_num) (by norm_num) (sr 2 235889 176917 (by norm_num) (by norm_num) (sr 6 176917 8293 (by norm_num) (by norm_num) (B 8293 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104843 : Reach 104843 := (sr 1 104843 157265 (by norm_num) (by norm_num) (sr 2 157265 117949 (by norm_num) (by norm_num) (sr 3 117949 44231 (by norm_num) (by norm_num) (B 44231 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104847 : Reach 104847 := (sr 1 104847 157271 (by norm_num) (by norm_num) (sr 1 157271 235907 (by norm_num) (by norm_num) (sr 1 235907 353861 (by norm_num) (by norm_num) (sr 4 353861 66349 (by norm_num) (by norm_num) (B 66349 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104851 : Reach 104851 := (sr 1 104851 157277 (by norm_num) (by norm_num) (sr 3 157277 58979 (by norm_num) (by norm_num) (B 58979 (by norm_num) (by norm_num) (by norm_num))))
theorem R104855 : Reach 104855 := (sr 1 104855 157283 (by norm_num) (by norm_num) (sr 1 157283 235925 (by norm_num) (by norm_num) (sr 6 235925 11059 (by norm_num) (by norm_num) (B 11059 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104859 : Reach 104859 := (sr 1 104859 157289 (by norm_num) (by norm_num) (sr 2 157289 117967 (by norm_num) (by norm_num) (sr 1 117967 176951 (by norm_num) (by norm_num) (sr 1 176951 265427 (by norm_num) (by norm_num) (sr 1 265427 398141 (by norm_num) (by norm_num) (sr 3 398141 149303 (by norm_num) (by norm_num) (sr 1 149303 223955 (by norm_num) (by norm_num) (sr 1 223955 335933 (by norm_num) (by norm_num) (sr 3 335933 125975 (by norm_num) (by norm_num) (sr 1 125975 188963 (by norm_num) (by norm_num) (sr 1 188963 283445 (by norm_num) (by norm_num) (sr 5 283445 26573 (by norm_num) (by norm_num) (B 26573 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R104863 : Reach 104863 := (sr 1 104863 157295 (by norm_num) (by norm_num) (sr 1 157295 235943 (by norm_num) (by norm_num) (sr 1 235943 353915 (by norm_num) (by norm_num) (sr 1 353915 530873 (by norm_num) (by norm_num) (sr 2 530873 398155 (by norm_num) (by norm_num) (sr 1 398155 597233 (by norm_num) (by norm_num) (sr 2 597233 447925 (by norm_num) (by norm_num) (sr 5 447925 41993 (by norm_num) (by norm_num) (B 41993 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R104867 : Reach 104867 := (sr 1 104867 157301 (by norm_num) (by norm_num) (sr 5 157301 14747 (by norm_num) (by norm_num) (B 14747 (by norm_num) (by norm_num) (by norm_num))))
theorem R104871 : Reach 104871 := (sr 1 104871 157307 (by norm_num) (by norm_num) (sr 1 157307 235961 (by norm_num) (by norm_num) (sr 2 235961 176971 (by norm_num) (by norm_num) (sr 1 176971 265457 (by norm_num) (by norm_num) (sr 2 265457 199093 (by norm_num) (by norm_num) (sr 5 199093 18665 (by norm_num) (by norm_num) (B 18665 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R104875 : Reach 104875 := (sr 1 104875 157313 (by norm_num) (by norm_num) (sr 2 157313 117985 (by norm_num) (by norm_num) (sr 2 117985 88489 (by norm_num) (by norm_num) (B 88489 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104879 : Reach 104879 := (sr 1 104879 157319 (by norm_num) (by norm_num) (sr 1 157319 235979 (by norm_num) (by norm_num) (sr 1 235979 353969 (by norm_num) (by norm_num) (sr 2 353969 265477 (by norm_num) (by norm_num) (sr 4 265477 49777 (by norm_num) (by norm_num) (B 49777 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104883 : Reach 104883 := (sr 1 104883 157325 (by norm_num) (by norm_num) (sr 3 157325 58997 (by norm_num) (by norm_num) (B 58997 (by norm_num) (by norm_num) (by norm_num))))
theorem R104887 : Reach 104887 := (sr 1 104887 157331 (by norm_num) (by norm_num) (sr 1 157331 235997 (by norm_num) (by norm_num) (sr 3 235997 88499 (by norm_num) (by norm_num) (B 88499 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104891 : Reach 104891 := (sr 1 104891 157337 (by norm_num) (by norm_num) (sr 2 157337 118003 (by norm_num) (by norm_num) (sr 1 118003 177005 (by norm_num) (by norm_num) (sr 3 177005 66377 (by norm_num) (by norm_num) (B 66377 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104895 : Reach 104895 := (sr 1 104895 157343 (by norm_num) (by norm_num) (sr 1 157343 236015 (by norm_num) (by norm_num) (sr 1 236015 354023 (by norm_num) (by norm_num) (sr 1 354023 531035 (by norm_num) (by norm_num) (sr 1 531035 796553 (by norm_num) (by norm_num) (sr 2 796553 597415 (by norm_num) (by norm_num) (sr 1 597415 896123 (by norm_num) (by norm_num) (sr 1 896123 1344185 (by norm_num) (by norm_num) (sr 2 1344185 1008139 (by norm_num) (by norm_num) (sr 1 1008139 1512209 (by norm_num) (by norm_num) (sr 2 1512209 1134157 (by norm_num) (by norm_num) (sr 3 1134157 425309 (by norm_num) (by norm_num) (sr 3 425309 159491 (by norm_num) (by norm_num) (sr 1 159491 239237 (by norm_num) (by norm_num) (sr 4 239237 44857 (by norm_num) (by norm_num) (B 44857 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R104899 : Reach 104899 := (sr 1 104899 157349 (by norm_num) (by norm_num) (sr 4 157349 29503 (by norm_num) (by norm_num) (B 29503 (by norm_num) (by norm_num) (by norm_num))))
theorem R104903 : Reach 104903 := (sr 1 104903 157355 (by norm_num) (by norm_num) (sr 1 157355 236033 (by norm_num) (by norm_num) (sr 2 236033 177025 (by norm_num) (by norm_num) (sr 2 177025 132769 (by norm_num) (by norm_num) (sr 2 132769 99577 (by norm_num) (by norm_num) (B 99577 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104907 : Reach 104907 := (sr 1 104907 157361 (by norm_num) (by norm_num) (sr 2 157361 118021 (by norm_num) (by norm_num) (sr 4 118021 22129 (by norm_num) (by norm_num) (B 22129 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104911 : Reach 104911 := (sr 1 104911 157367 (by norm_num) (by norm_num) (sr 1 157367 236051 (by norm_num) (by norm_num) (sr 1 236051 354077 (by norm_num) (by norm_num) (sr 3 354077 132779 (by norm_num) (by norm_num) (sr 1 132779 199169 (by norm_num) (by norm_num) (sr 2 199169 149377 (by norm_num) (by norm_num) (sr 2 149377 112033 (by norm_num) (by norm_num) (sr 2 112033 84025 (by norm_num) (by norm_num) (B 84025 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R104915 : Reach 104915 := (sr 1 104915 157373 (by norm_num) (by norm_num) (sr 3 157373 59015 (by norm_num) (by norm_num) (B 59015 (by norm_num) (by norm_num) (by norm_num))))
theorem R104919 : Reach 104919 := (sr 1 104919 157379 (by norm_num) (by norm_num) (sr 1 157379 236069 (by norm_num) (by norm_num) (sr 4 236069 44263 (by norm_num) (by norm_num) (B 44263 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104923 : Reach 104923 := (sr 1 104923 157385 (by norm_num) (by norm_num) (sr 2 157385 118039 (by norm_num) (by norm_num) (sr 1 118039 177059 (by norm_num) (by norm_num) (sr 1 177059 265589 (by norm_num) (by norm_num) (sr 5 265589 24899 (by norm_num) (by norm_num) (B 24899 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R104927 : Reach 104927 := (sr 1 104927 157391 (by norm_num) (by norm_num) (sr 1 157391 236087 (by norm_num) (by norm_num) (sr 1 236087 354131 (by norm_num) (by norm_num) (sr 1 354131 531197 (by norm_num) (by norm_num) (sr 3 531197 199199 (by norm_num) (by norm_num) (sr 1 199199 298799 (by norm_num) (by norm_num) (sr 1 298799 448199 (by norm_num) (by norm_num) (sr 1 448199 672299 (by norm_num) (by norm_num) (sr 1 672299 1008449 (by norm_num) (by norm_num) (sr 2 1008449 756337 (by norm_num) (by norm_num) (sr 2 756337 567253 (by norm_num) (by norm_num) (sr 7 567253 13295 (by norm_num) (by norm_num) (B 13295 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R104931 : Reach 104931 := (sr 1 104931 157397 (by norm_num) (by norm_num) (sr 7 157397 3689 (by norm_num) (by norm_num) (B 3689 (by norm_num) (by norm_num) (by norm_num))))
theorem R104935 : Reach 104935 := (sr 1 104935 157403 (by norm_num) (by norm_num) (sr 1 157403 236105 (by norm_num) (by norm_num) (sr 2 236105 177079 (by norm_num) (by norm_num) (sr 1 177079 265619 (by norm_num) (by norm_num) (sr 1 265619 398429 (by norm_num) (by norm_num) (sr 3 398429 149411 (by norm_num) (by norm_num) (sr 1 149411 224117 (by norm_num) (by norm_num) (sr 5 224117 21011 (by norm_num) (by norm_num) (B 21011 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R104939 : Reach 104939 := (sr 1 104939 157409 (by norm_num) (by norm_num) (sr 2 157409 118057 (by norm_num) (by norm_num) (sr 2 118057 88543 (by norm_num) (by norm_num) (B 88543 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104943 : Reach 104943 := (sr 1 104943 157415 (by norm_num) (by norm_num) (sr 1 157415 236123 (by norm_num) (by norm_num) (sr 1 236123 354185 (by norm_num) (by norm_num) (sr 2 354185 265639 (by norm_num) (by norm_num) (sr 1 265639 398459 (by norm_num) (by norm_num) (sr 1 398459 597689 (by norm_num) (by norm_num) (sr 2 597689 448267 (by norm_num) (by norm_num) (sr 1 448267 672401 (by norm_num) (by norm_num) (sr 2 672401 504301 (by norm_num) (by norm_num) (sr 3 504301 189113 (by norm_num) (by norm_num) (sr 2 189113 141835 (by norm_num) (by norm_num) (sr 1 141835 212753 (by norm_num) (by norm_num) (sr 2 212753 159565 (by norm_num) (by norm_num) (sr 3 159565 59837 (by norm_num) (by norm_num) (B 59837 (by norm_num) (by norm_num) (by norm_num))))))))))))))))
theorem R104947 : Reach 104947 := (sr 1 104947 157421 (by norm_num) (by norm_num) (sr 3 157421 59033 (by norm_num) (by norm_num) (B 59033 (by norm_num) (by norm_num) (by norm_num))))
theorem R104951 : Reach 104951 := (sr 1 104951 157427 (by norm_num) (by norm_num) (sr 1 157427 236141 (by norm_num) (by norm_num) (sr 3 236141 88553 (by norm_num) (by norm_num) (B 88553 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104955 : Reach 104955 := (sr 1 104955 157433 (by norm_num) (by norm_num) (sr 2 157433 118075 (by norm_num) (by norm_num) (sr 1 118075 177113 (by norm_num) (by norm_num) (sr 2 177113 132835 (by norm_num) (by norm_num) (sr 1 132835 199253 (by norm_num) (by norm_num) (sr 8 199253 2335 (by norm_num) (by norm_num) (B 2335 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R104959 : Reach 104959 := (sr 1 104959 157439 (by norm_num) (by norm_num) (sr 1 157439 236159 (by norm_num) (by norm_num) (sr 1 236159 354239 (by norm_num) (by norm_num) (sr 1 354239 531359 (by norm_num) (by norm_num) (sr 1 531359 797039 (by norm_num) (by norm_num) (sr 1 797039 1195559 (by norm_num) (by norm_num) (sr 1 1195559 1793339 (by norm_num) (by norm_num) (sr 1 1793339 2690009 (by norm_num) (by norm_num) (sr 2 2690009 2017507 (by norm_num) (by norm_num) (sr 1 2017507 3026261 (by norm_num) (by norm_num) (sr 11 3026261 4433 (by norm_num) (by norm_num) (B 4433 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R104963 : Reach 104963 := (sr 1 104963 157445 (by norm_num) (by norm_num) (sr 4 157445 29521 (by norm_num) (by norm_num) (B 29521 (by norm_num) (by norm_num) (by norm_num))))
theorem R104967 : Reach 104967 := (sr 1 104967 157451 (by norm_num) (by norm_num) (sr 1 157451 236177 (by norm_num) (by norm_num) (sr 2 236177 177133 (by norm_num) (by norm_num) (sr 3 177133 66425 (by norm_num) (by norm_num) (B 66425 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104971 : Reach 104971 := (sr 1 104971 157457 (by norm_num) (by norm_num) (sr 2 157457 118093 (by norm_num) (by norm_num) (sr 3 118093 44285 (by norm_num) (by norm_num) (B 44285 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104975 : Reach 104975 := (sr 1 104975 157463 (by norm_num) (by norm_num) (sr 1 157463 236195 (by norm_num) (by norm_num) (sr 1 236195 354293 (by norm_num) (by norm_num) (sr 5 354293 33215 (by norm_num) (by norm_num) (B 33215 (by norm_num) (by norm_num) (by norm_num))))))
theorem R104979 : Reach 104979 := (sr 1 104979 157469 (by norm_num) (by norm_num) (sr 3 157469 59051 (by norm_num) (by norm_num) (B 59051 (by norm_num) (by norm_num) (by norm_num))))
theorem R104983 : Reach 104983 := (sr 1 104983 157475 (by norm_num) (by norm_num) (sr 1 157475 236213 (by norm_num) (by norm_num) (sr 5 236213 22145 (by norm_num) (by norm_num) (B 22145 (by norm_num) (by norm_num) (by norm_num)))))
theorem R104987 : Reach 104987 := (sr 1 104987 157481 (by norm_num) (by norm_num) (sr 2 157481 118111 (by norm_num) (by norm_num) (sr 1 118111 177167 (by norm_num) (by norm_num) (sr 1 177167 265751 (by norm_num) (by norm_num) (sr 1 265751 398627 (by norm_num) (by norm_num) (sr 1 398627 597941 (by norm_num) (by norm_num) (sr 5 597941 56057 (by norm_num) (by norm_num) (B 56057 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R104991 : Reach 104991 := (sr 1 104991 157487 (by norm_num) (by norm_num) (sr 1 157487 236231 (by norm_num) (by norm_num) (sr 1 236231 354347 (by norm_num) (by norm_num) (sr 1 354347 531521 (by norm_num) (by norm_num) (sr 2 531521 398641 (by norm_num) (by norm_num) (sr 2 398641 298981 (by norm_num) (by norm_num) (sr 4 298981 56059 (by norm_num) (by norm_num) (B 56059 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R104995 : Reach 104995 := (sr 1 104995 157493 (by norm_num) (by norm_num) (sr 5 157493 14765 (by norm_num) (by norm_num) (B 14765 (by norm_num) (by norm_num) (by norm_num))))
theorem R104999 : Reach 104999 := (sr 1 104999 157499 (by norm_num) (by norm_num) (sr 1 157499 236249 (by norm_num) (by norm_num) (sr 2 236249 177187 (by norm_num) (by norm_num) (sr 1 177187 265781 (by norm_num) (by norm_num) (sr 5 265781 24917 (by norm_num) (by norm_num) (B 24917 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R105003 : Reach 105003 := (sr 1 105003 157505 (by norm_num) (by norm_num) (sr 2 157505 118129 (by norm_num) (by norm_num) (sr 2 118129 88597 (by norm_num) (by norm_num) (B 88597 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105007 : Reach 105007 := (sr 1 105007 157511 (by norm_num) (by norm_num) (sr 1 157511 236267 (by norm_num) (by norm_num) (sr 1 236267 354401 (by norm_num) (by norm_num) (sr 2 354401 265801 (by norm_num) (by norm_num) (sr 2 265801 199351 (by norm_num) (by norm_num) (sr 1 199351 299027 (by norm_num) (by norm_num) (sr 1 299027 448541 (by norm_num) (by norm_num) (sr 3 448541 168203 (by norm_num) (by norm_num) (sr 1 168203 252305 (by norm_num) (by norm_num) (sr 2 252305 189229 (by norm_num) (by norm_num) (sr 3 189229 70961 (by norm_num) (by norm_num) (B 70961 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R105011 : Reach 105011 := (sr 1 105011 157517 (by norm_num) (by norm_num) (sr 3 157517 59069 (by norm_num) (by norm_num) (B 59069 (by norm_num) (by norm_num) (by norm_num))))
theorem R105015 : Reach 105015 := (sr 1 105015 157523 (by norm_num) (by norm_num) (sr 1 157523 236285 (by norm_num) (by norm_num) (sr 3 236285 88607 (by norm_num) (by norm_num) (B 88607 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105019 : Reach 105019 := (sr 1 105019 157529 (by norm_num) (by norm_num) (sr 2 157529 118147 (by norm_num) (by norm_num) (sr 1 118147 177221 (by norm_num) (by norm_num) (sr 4 177221 33229 (by norm_num) (by norm_num) (B 33229 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105023 : Reach 105023 := (sr 1 105023 157535 (by norm_num) (by norm_num) (sr 1 157535 236303 (by norm_num) (by norm_num) (sr 1 236303 354455 (by norm_num) (by norm_num) (sr 1 354455 531683 (by norm_num) (by norm_num) (sr 1 531683 797525 (by norm_num) (by norm_num) (sr 9 797525 4673 (by norm_num) (by norm_num) (B 4673 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105027 : Reach 105027 := (sr 1 105027 157541 (by norm_num) (by norm_num) (sr 4 157541 29539 (by norm_num) (by norm_num) (B 29539 (by norm_num) (by norm_num) (by norm_num))))
theorem R105031 : Reach 105031 := (sr 1 105031 157547 (by norm_num) (by norm_num) (sr 1 157547 236321 (by norm_num) (by norm_num) (sr 2 236321 177241 (by norm_num) (by norm_num) (sr 2 177241 132931 (by norm_num) (by norm_num) (sr 1 132931 199397 (by norm_num) (by norm_num) (sr 4 199397 37387 (by norm_num) (by norm_num) (B 37387 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105035 : Reach 105035 := (sr 1 105035 157553 (by norm_num) (by norm_num) (sr 2 157553 118165 (by norm_num) (by norm_num) (sr 6 118165 5539 (by norm_num) (by norm_num) (B 5539 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105039 : Reach 105039 := (sr 1 105039 157559 (by norm_num) (by norm_num) (sr 1 157559 236339 (by norm_num) (by norm_num) (sr 1 236339 354509 (by norm_num) (by norm_num) (sr 3 354509 132941 (by norm_num) (by norm_num) (sr 3 132941 49853 (by norm_num) (by norm_num) (B 49853 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R105043 : Reach 105043 := (sr 1 105043 157565 (by norm_num) (by norm_num) (sr 3 157565 59087 (by norm_num) (by norm_num) (B 59087 (by norm_num) (by norm_num) (by norm_num))))
theorem R105047 : Reach 105047 := (sr 1 105047 157571 (by norm_num) (by norm_num) (sr 1 157571 236357 (by norm_num) (by norm_num) (sr 4 236357 44317 (by norm_num) (by norm_num) (B 44317 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105051 : Reach 105051 := (sr 1 105051 157577 (by norm_num) (by norm_num) (sr 2 157577 118183 (by norm_num) (by norm_num) (sr 1 118183 177275 (by norm_num) (by norm_num) (sr 1 177275 265913 (by norm_num) (by norm_num) (sr 2 265913 199435 (by norm_num) (by norm_num) (sr 1 199435 299153 (by norm_num) (by norm_num) (sr 2 299153 224365 (by norm_num) (by norm_num) (sr 3 224365 84137 (by norm_num) (by norm_num) (B 84137 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R105055 : Reach 105055 := (sr 1 105055 157583 (by norm_num) (by norm_num) (sr 1 157583 236375 (by norm_num) (by norm_num) (sr 1 236375 354563 (by norm_num) (by norm_num) (sr 1 354563 531845 (by norm_num) (by norm_num) (sr 4 531845 99721 (by norm_num) (by norm_num) (B 99721 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R105059 : Reach 105059 := (sr 1 105059 157589 (by norm_num) (by norm_num) (sr 6 157589 7387 (by norm_num) (by norm_num) (B 7387 (by norm_num) (by norm_num) (by norm_num))))
theorem R105063 : Reach 105063 := (sr 1 105063 157595 (by norm_num) (by norm_num) (sr 1 157595 236393 (by norm_num) (by norm_num) (sr 2 236393 177295 (by norm_num) (by norm_num) (sr 1 177295 265943 (by norm_num) (by norm_num) (sr 1 265943 398915 (by norm_num) (by norm_num) (sr 1 398915 598373 (by norm_num) (by norm_num) (sr 4 598373 112195 (by norm_num) (by norm_num) (sr 1 112195 168293 (by norm_num) (by norm_num) (sr 4 168293 31555 (by norm_num) (by norm_num) (B 31555 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R105067 : Reach 105067 := (sr 1 105067 157601 (by norm_num) (by norm_num) (sr 2 157601 118201 (by norm_num) (by norm_num) (sr 2 118201 88651 (by norm_num) (by norm_num) (B 88651 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105071 : Reach 105071 := (sr 1 105071 157607 (by norm_num) (by norm_num) (sr 1 157607 236411 (by norm_num) (by norm_num) (sr 1 236411 354617 (by norm_num) (by norm_num) (sr 2 354617 265963 (by norm_num) (by norm_num) (sr 1 265963 398945 (by norm_num) (by norm_num) (sr 2 398945 299209 (by norm_num) (by norm_num) (sr 2 299209 224407 (by norm_num) (by norm_num) (sr 1 224407 336611 (by norm_num) (by norm_num) (sr 1 336611 504917 (by norm_num) (by norm_num) (sr 8 504917 5917 (by norm_num) (by norm_num) (B 5917 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R105075 : Reach 105075 := (sr 1 105075 157613 (by norm_num) (by norm_num) (sr 3 157613 59105 (by norm_num) (by norm_num) (B 59105 (by norm_num) (by norm_num) (by norm_num))))
theorem R105079 : Reach 105079 := (sr 1 105079 157619 (by norm_num) (by norm_num) (sr 1 157619 236429 (by norm_num) (by norm_num) (sr 3 236429 88661 (by norm_num) (by norm_num) (B 88661 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105083 : Reach 105083 := (sr 1 105083 157625 (by norm_num) (by norm_num) (sr 2 157625 118219 (by norm_num) (by norm_num) (sr 1 118219 177329 (by norm_num) (by norm_num) (sr 2 177329 132997 (by norm_num) (by norm_num) (sr 4 132997 24937 (by norm_num) (by norm_num) (B 24937 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R105087 : Reach 105087 := (sr 1 105087 157631 (by norm_num) (by norm_num) (sr 1 157631 236447 (by norm_num) (by norm_num) (sr 1 236447 354671 (by norm_num) (by norm_num) (sr 1 354671 532007 (by norm_num) (by norm_num) (sr 1 532007 798011 (by norm_num) (by norm_num) (sr 1 798011 1197017 (by norm_num) (by norm_num) (sr 2 1197017 897763 (by norm_num) (by norm_num) (sr 1 897763 1346645 (by norm_num) (by norm_num) (sr 8 1346645 15781 (by norm_num) (by norm_num) (B 15781 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R105091 : Reach 105091 := (sr 1 105091 157637 (by norm_num) (by norm_num) (sr 4 157637 29557 (by norm_num) (by norm_num) (B 29557 (by norm_num) (by norm_num) (by norm_num))))
theorem R105095 : Reach 105095 := (sr 1 105095 157643 (by norm_num) (by norm_num) (sr 1 157643 236465 (by norm_num) (by norm_num) (sr 2 236465 177349 (by norm_num) (by norm_num) (sr 4 177349 33253 (by norm_num) (by norm_num) (B 33253 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105099 : Reach 105099 := (sr 1 105099 157649 (by norm_num) (by norm_num) (sr 2 157649 118237 (by norm_num) (by norm_num) (sr 3 118237 44339 (by norm_num) (by norm_num) (B 44339 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105103 : Reach 105103 := (sr 1 105103 157655 (by norm_num) (by norm_num) (sr 1 157655 236483 (by norm_num) (by norm_num) (sr 1 236483 354725 (by norm_num) (by norm_num) (sr 4 354725 66511 (by norm_num) (by norm_num) (B 66511 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105107 : Reach 105107 := (sr 1 105107 157661 (by norm_num) (by norm_num) (sr 3 157661 59123 (by norm_num) (by norm_num) (B 59123 (by norm_num) (by norm_num) (by norm_num))))
theorem R105111 : Reach 105111 := (sr 1 105111 157667 (by norm_num) (by norm_num) (sr 1 157667 236501 (by norm_num) (by norm_num) (sr 7 236501 5543 (by norm_num) (by norm_num) (B 5543 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105115 : Reach 105115 := (sr 1 105115 157673 (by norm_num) (by norm_num) (sr 2 157673 118255 (by norm_num) (by norm_num) (sr 1 118255 177383 (by norm_num) (by norm_num) (sr 1 177383 266075 (by norm_num) (by norm_num) (sr 1 266075 399113 (by norm_num) (by norm_num) (sr 2 399113 299335 (by norm_num) (by norm_num) (sr 1 299335 449003 (by norm_num) (by norm_num) (sr 1 449003 673505 (by norm_num) (by norm_num) (sr 2 673505 505129 (by norm_num) (by norm_num) (sr 2 505129 378847 (by norm_num) (by norm_num) (sr 1 378847 568271 (by norm_num) (by norm_num) (sr 1 568271 852407 (by norm_num) (by norm_num) (sr 1 852407 1278611 (by norm_num) (by norm_num) (sr 1 1278611 1917917 (by norm_num) (by norm_num) (sr 3 1917917 719219 (by norm_num) (by norm_num) (sr 1 719219 1078829 (by norm_num) (by norm_num) (sr 3 1078829 404561 (by norm_num) (by norm_num) (sr 2 404561 303421 (by norm_num) (by norm_num) (sr 3 303421 113783 (by norm_num) (by norm_num) (sr 1 113783 170675 (by norm_num) (by norm_num) (sr 1 170675 256013 (by norm_num) (by norm_num) (sr 3 256013 96005 (by norm_num) (by norm_num) (B 96005 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R105119 : Reach 105119 := (sr 1 105119 157679 (by norm_num) (by norm_num) (sr 1 157679 236519 (by norm_num) (by norm_num) (sr 1 236519 354779 (by norm_num) (by norm_num) (sr 1 354779 532169 (by norm_num) (by norm_num) (sr 2 532169 399127 (by norm_num) (by norm_num) (sr 1 399127 598691 (by norm_num) (by norm_num) (sr 1 598691 898037 (by norm_num) (by norm_num) (sr 5 898037 84191 (by norm_num) (by norm_num) (B 84191 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R105123 : Reach 105123 := (sr 1 105123 157685 (by norm_num) (by norm_num) (sr 5 157685 14783 (by norm_num) (by norm_num) (B 14783 (by norm_num) (by norm_num) (by norm_num))))
theorem R105127 : Reach 105127 := (sr 1 105127 157691 (by norm_num) (by norm_num) (sr 1 157691 236537 (by norm_num) (by norm_num) (sr 2 236537 177403 (by norm_num) (by norm_num) (sr 1 177403 266105 (by norm_num) (by norm_num) (sr 2 266105 199579 (by norm_num) (by norm_num) (sr 1 199579 299369 (by norm_num) (by norm_num) (sr 2 299369 224527 (by norm_num) (by norm_num) (sr 1 224527 336791 (by norm_num) (by norm_num) (sr 1 336791 505187 (by norm_num) (by norm_num) (sr 1 505187 757781 (by norm_num) (by norm_num) (sr 6 757781 35521 (by norm_num) (by norm_num) (B 35521 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R105131 : Reach 105131 := (sr 1 105131 157697 (by norm_num) (by norm_num) (sr 2 157697 118273 (by norm_num) (by norm_num) (sr 2 118273 88705 (by norm_num) (by norm_num) (B 88705 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105135 : Reach 105135 := (sr 1 105135 157703 (by norm_num) (by norm_num) (sr 1 157703 236555 (by norm_num) (by norm_num) (sr 1 236555 354833 (by norm_num) (by norm_num) (sr 2 354833 266125 (by norm_num) (by norm_num) (sr 3 266125 99797 (by norm_num) (by norm_num) (sr 7 99797 2339 (by norm_num) (by norm_num) (B 2339 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105139 : Reach 105139 := (sr 1 105139 157709 (by norm_num) (by norm_num) (sr 3 157709 59141 (by norm_num) (by norm_num) (B 59141 (by norm_num) (by norm_num) (by norm_num))))
theorem R105143 : Reach 105143 := (sr 1 105143 157715 (by norm_num) (by norm_num) (sr 1 157715 236573 (by norm_num) (by norm_num) (sr 3 236573 88715 (by norm_num) (by norm_num) (B 88715 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105147 : Reach 105147 := (sr 1 105147 157721 (by norm_num) (by norm_num) (sr 2 157721 118291 (by norm_num) (by norm_num) (sr 1 118291 177437 (by norm_num) (by norm_num) (sr 3 177437 66539 (by norm_num) (by norm_num) (B 66539 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105151 : Reach 105151 := (sr 1 105151 157727 (by norm_num) (by norm_num) (sr 1 157727 236591 (by norm_num) (by norm_num) (sr 1 236591 354887 (by norm_num) (by norm_num) (sr 1 354887 532331 (by norm_num) (by norm_num) (sr 1 532331 798497 (by norm_num) (by norm_num) (sr 2 798497 598873 (by norm_num) (by norm_num) (sr 2 598873 449155 (by norm_num) (by norm_num) (sr 1 449155 673733 (by norm_num) (by norm_num) (sr 4 673733 126325 (by norm_num) (by norm_num) (sr 5 126325 11843 (by norm_num) (by norm_num) (B 11843 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R105155 : Reach 105155 := (sr 1 105155 157733 (by norm_num) (by norm_num) (sr 4 157733 29575 (by norm_num) (by norm_num) (B 29575 (by norm_num) (by norm_num) (by norm_num))))
theorem R105159 : Reach 105159 := (sr 1 105159 157739 (by norm_num) (by norm_num) (sr 1 157739 236609 (by norm_num) (by norm_num) (sr 2 236609 177457 (by norm_num) (by norm_num) (sr 2 177457 133093 (by norm_num) (by norm_num) (sr 4 133093 24955 (by norm_num) (by norm_num) (B 24955 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R105163 : Reach 105163 := (sr 1 105163 157745 (by norm_num) (by norm_num) (sr 2 157745 118309 (by norm_num) (by norm_num) (sr 4 118309 22183 (by norm_num) (by norm_num) (B 22183 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105167 : Reach 105167 := (sr 1 105167 157751 (by norm_num) (by norm_num) (sr 1 157751 236627 (by norm_num) (by norm_num) (sr 1 236627 354941 (by norm_num) (by norm_num) (sr 3 354941 133103 (by norm_num) (by norm_num) (sr 1 133103 199655 (by norm_num) (by norm_num) (sr 1 199655 299483 (by norm_num) (by norm_num) (sr 1 299483 449225 (by norm_num) (by norm_num) (sr 2 449225 336919 (by norm_num) (by norm_num) (sr 1 336919 505379 (by norm_num) (by norm_num) (sr 1 505379 758069 (by norm_num) (by norm_num) (sr 5 758069 71069 (by norm_num) (by norm_num) (B 71069 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R105171 : Reach 105171 := (sr 1 105171 157757 (by norm_num) (by norm_num) (sr 3 157757 59159 (by norm_num) (by norm_num) (B 59159 (by norm_num) (by norm_num) (by norm_num))))
theorem R105175 : Reach 105175 := (sr 1 105175 157763 (by norm_num) (by norm_num) (sr 1 157763 236645 (by norm_num) (by norm_num) (sr 4 236645 44371 (by norm_num) (by norm_num) (B 44371 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105179 : Reach 105179 := (sr 1 105179 157769 (by norm_num) (by norm_num) (sr 2 157769 118327 (by norm_num) (by norm_num) (sr 1 118327 177491 (by norm_num) (by norm_num) (sr 1 177491 266237 (by norm_num) (by norm_num) (sr 3 266237 99839 (by norm_num) (by norm_num) R99839)))))
theorem R105183 : Reach 105183 := (sr 1 105183 157775 (by norm_num) (by norm_num) (sr 1 157775 236663 (by norm_num) (by norm_num) (sr 1 236663 354995 (by norm_num) (by norm_num) (sr 1 354995 532493 (by norm_num) (by norm_num) (sr 3 532493 199685 (by norm_num) (by norm_num) (sr 4 199685 37441 (by norm_num) (by norm_num) (B 37441 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105187 : Reach 105187 := (sr 1 105187 157781 (by norm_num) (by norm_num) (sr 8 157781 1849 (by norm_num) (by norm_num) (B 1849 (by norm_num) (by norm_num) (by norm_num))))
theorem R105191 : Reach 105191 := (sr 1 105191 157787 (by norm_num) (by norm_num) (sr 1 157787 236681 (by norm_num) (by norm_num) (sr 2 236681 177511 (by norm_num) (by norm_num) (sr 1 177511 266267 (by norm_num) (by norm_num) (sr 1 266267 399401 (by norm_num) (by norm_num) (sr 2 399401 299551 (by norm_num) (by norm_num) (sr 1 299551 449327 (by norm_num) (by norm_num) (sr 1 449327 673991 (by norm_num) (by norm_num) (sr 1 673991 1010987 (by norm_num) (by norm_num) (sr 1 1010987 1516481 (by norm_num) (by norm_num) (sr 2 1516481 1137361 (by norm_num) (by norm_num) (sr 2 1137361 853021 (by norm_num) (by norm_num) (sr 3 853021 319883 (by norm_num) (by norm_num) (sr 1 319883 479825 (by norm_num) (by norm_num) (sr 2 479825 359869 (by norm_num) (by norm_num) (sr 3 359869 134951 (by norm_num) (by norm_num) (sr 1 134951 202427 (by norm_num) (by norm_num) (sr 1 202427 303641 (by norm_num) (by norm_num) (sr 2 303641 227731 (by norm_num) (by norm_num) (sr 1 227731 341597 (by norm_num) (by norm_num) (sr 3 341597 128099 (by norm_num) (by norm_num) (sr 1 128099 192149 (by norm_num) (by norm_num) (sr 6 192149 9007 (by norm_num) (by norm_num) (B 9007 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))
theorem R105195 : Reach 105195 := (sr 1 105195 157793 (by norm_num) (by norm_num) (sr 2 157793 118345 (by norm_num) (by norm_num) (sr 2 118345 88759 (by norm_num) (by norm_num) (B 88759 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105199 : Reach 105199 := (sr 1 105199 157799 (by norm_num) (by norm_num) (sr 1 157799 236699 (by norm_num) (by norm_num) (sr 1 236699 355049 (by norm_num) (by norm_num) (sr 2 355049 266287 (by norm_num) (by norm_num) (sr 1 266287 399431 (by norm_num) (by norm_num) (sr 1 399431 599147 (by norm_num) (by norm_num) (sr 1 599147 898721 (by norm_num) (by norm_num) (sr 2 898721 674041 (by norm_num) (by norm_num) (sr 2 674041 505531 (by norm_num) (by norm_num) (sr 1 505531 758297 (by norm_num) (by norm_num) (sr 2 758297 568723 (by norm_num) (by norm_num) (sr 1 568723 853085 (by norm_num) (by norm_num) (sr 3 853085 319907 (by norm_num) (by norm_num) (sr 1 319907 479861 (by norm_num) (by norm_num) (sr 5 479861 44987 (by norm_num) (by norm_num) (B 44987 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R105203 : Reach 105203 := (sr 1 105203 157805 (by norm_num) (by norm_num) (sr 3 157805 59177 (by norm_num) (by norm_num) (B 59177 (by norm_num) (by norm_num) (by norm_num))))
theorem R105207 : Reach 105207 := (sr 1 105207 157811 (by norm_num) (by norm_num) (sr 1 157811 236717 (by norm_num) (by norm_num) (sr 3 236717 88769 (by norm_num) (by norm_num) (B 88769 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105211 : Reach 105211 := (sr 1 105211 157817 (by norm_num) (by norm_num) (sr 2 157817 118363 (by norm_num) (by norm_num) (sr 1 118363 177545 (by norm_num) (by norm_num) (sr 2 177545 133159 (by norm_num) (by norm_num) (sr 1 133159 199739 (by norm_num) (by norm_num) (sr 1 199739 299609 (by norm_num) (by norm_num) (sr 2 299609 224707 (by norm_num) (by norm_num) (sr 1 224707 337061 (by norm_num) (by norm_num) (sr 4 337061 63199 (by norm_num) (by norm_num) (B 63199 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R105215 : Reach 105215 := (sr 1 105215 157823 (by norm_num) (by norm_num) (sr 1 157823 236735 (by norm_num) (by norm_num) (sr 1 236735 355103 (by norm_num) (by norm_num) (sr 1 355103 532655 (by norm_num) (by norm_num) (sr 1 532655 798983 (by norm_num) (by norm_num) (sr 1 798983 1198475 (by norm_num) (by norm_num) (sr 1 1198475 1797713 (by norm_num) (by norm_num) (sr 2 1797713 1348285 (by norm_num) (by norm_num) (sr 3 1348285 505607 (by norm_num) (by norm_num) (sr 1 505607 758411 (by norm_num) (by norm_num) (sr 1 758411 1137617 (by norm_num) (by norm_num) (sr 2 1137617 853213 (by norm_num) (by norm_num) (sr 3 853213 319955 (by norm_num) (by norm_num) (sr 1 319955 479933 (by norm_num) (by norm_num) (sr 3 479933 179975 (by norm_num) (by norm_num) (sr 1 179975 269963 (by norm_num) (by norm_num) (sr 1 269963 404945 (by norm_num) (by norm_num) (sr 2 404945 303709 (by norm_num) (by norm_num) (sr 3 303709 113891 (by norm_num) (by norm_num) (sr 1 113891 170837 (by norm_num) (by norm_num) (sr 9 170837 1001 (by norm_num) (by norm_num) (B 1001 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))
theorem R105219 : Reach 105219 := (sr 1 105219 157829 (by norm_num) (by norm_num) (sr 4 157829 29593 (by norm_num) (by norm_num) (B 29593 (by norm_num) (by norm_num) (by norm_num))))
theorem R105223 : Reach 105223 := (sr 1 105223 157835 (by norm_num) (by norm_num) (sr 1 157835 236753 (by norm_num) (by norm_num) (sr 2 236753 177565 (by norm_num) (by norm_num) (sr 3 177565 66587 (by norm_num) (by norm_num) (B 66587 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105227 : Reach 105227 := (sr 1 105227 157841 (by norm_num) (by norm_num) (sr 2 157841 118381 (by norm_num) (by norm_num) (sr 3 118381 44393 (by norm_num) (by norm_num) (B 44393 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105231 : Reach 105231 := (sr 1 105231 157847 (by norm_num) (by norm_num) (sr 1 157847 236771 (by norm_num) (by norm_num) (sr 1 236771 355157 (by norm_num) (by norm_num) (sr 9 355157 2081 (by norm_num) (by norm_num) (B 2081 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105235 : Reach 105235 := (sr 1 105235 157853 (by norm_num) (by norm_num) (sr 3 157853 59195 (by norm_num) (by norm_num) (B 59195 (by norm_num) (by norm_num) (by norm_num))))
theorem R105239 : Reach 105239 := (sr 1 105239 157859 (by norm_num) (by norm_num) (sr 1 157859 236789 (by norm_num) (by norm_num) (sr 5 236789 22199 (by norm_num) (by norm_num) (B 22199 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105243 : Reach 105243 := (sr 1 105243 157865 (by norm_num) (by norm_num) (sr 2 157865 118399 (by norm_num) (by norm_num) (sr 1 118399 177599 (by norm_num) (by norm_num) (sr 1 177599 266399 (by norm_num) (by norm_num) (sr 1 266399 399599 (by norm_num) (by norm_num) (sr 1 399599 599399 (by norm_num) (by norm_num) (sr 1 599399 899099 (by norm_num) (by norm_num) (sr 1 899099 1348649 (by norm_num) (by norm_num) (sr 2 1348649 1011487 (by norm_num) (by norm_num) (sr 1 1011487 1517231 (by norm_num) (by norm_num) (sr 1 1517231 2275847 (by norm_num) (by norm_num) (sr 1 2275847 3413771 (by norm_num) (by norm_num) (sr 1 3413771 5120657 (by norm_num) (by norm_num) (sr 2 5120657 3840493 (by norm_num) (by norm_num) (sr 3 3840493 1440185 (by norm_num) (by norm_num) (sr 2 1440185 1080139 (by norm_num) (by norm_num) (sr 1 1080139 1620209 (by norm_num) (by norm_num) (sr 2 1620209 1215157 (by norm_num) (by norm_num) (sr 5 1215157 113921 (by norm_num) (by norm_num) (sr 2 113921 85441 (by norm_num) (by norm_num) (B 85441 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))
theorem R105247 : Reach 105247 := (sr 1 105247 157871 (by norm_num) (by norm_num) (sr 1 157871 236807 (by norm_num) (by norm_num) (sr 1 236807 355211 (by norm_num) (by norm_num) (sr 1 355211 532817 (by norm_num) (by norm_num) (sr 2 532817 399613 (by norm_num) (by norm_num) (sr 3 399613 149855 (by norm_num) (by norm_num) (sr 1 149855 224783 (by norm_num) (by norm_num) (sr 1 224783 337175 (by norm_num) (by norm_num) (sr 1 337175 505763 (by norm_num) (by norm_num) (sr 1 505763 758645 (by norm_num) (by norm_num) (sr 5 758645 71123 (by norm_num) (by norm_num) (B 71123 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R105251 : Reach 105251 := (sr 1 105251 157877 (by norm_num) (by norm_num) (sr 5 157877 14801 (by norm_num) (by norm_num) (B 14801 (by norm_num) (by norm_num) (by norm_num))))
theorem R105255 : Reach 105255 := (sr 1 105255 157883 (by norm_num) (by norm_num) (sr 1 157883 236825 (by norm_num) (by norm_num) (sr 2 236825 177619 (by norm_num) (by norm_num) (sr 1 177619 266429 (by norm_num) (by norm_num) (sr 3 266429 99911 (by norm_num) (by norm_num) R99911)))))
theorem R105259 : Reach 105259 := (sr 1 105259 157889 (by norm_num) (by norm_num) (sr 2 157889 118417 (by norm_num) (by norm_num) (sr 2 118417 88813 (by norm_num) (by norm_num) (B 88813 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105263 : Reach 105263 := (sr 1 105263 157895 (by norm_num) (by norm_num) (sr 1 157895 236843 (by norm_num) (by norm_num) (sr 1 236843 355265 (by norm_num) (by norm_num) (sr 2 355265 266449 (by norm_num) (by norm_num) (sr 2 266449 199837 (by norm_num) (by norm_num) (sr 3 199837 74939 (by norm_num) (by norm_num) (B 74939 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105267 : Reach 105267 := (sr 1 105267 157901 (by norm_num) (by norm_num) (sr 3 157901 59213 (by norm_num) (by norm_num) (B 59213 (by norm_num) (by norm_num) (by norm_num))))
theorem R105271 : Reach 105271 := (sr 1 105271 157907 (by norm_num) (by norm_num) (sr 1 157907 236861 (by norm_num) (by norm_num) (sr 3 236861 88823 (by norm_num) (by norm_num) (B 88823 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105275 : Reach 105275 := (sr 1 105275 157913 (by norm_num) (by norm_num) (sr 2 157913 118435 (by norm_num) (by norm_num) (sr 1 118435 177653 (by norm_num) (by norm_num) (sr 5 177653 16655 (by norm_num) (by norm_num) (B 16655 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105279 : Reach 105279 := (sr 1 105279 157919 (by norm_num) (by norm_num) (sr 1 157919 236879 (by norm_num) (by norm_num) (sr 1 236879 355319 (by norm_num) (by norm_num) (sr 1 355319 532979 (by norm_num) (by norm_num) (sr 1 532979 799469 (by norm_num) (by norm_num) (sr 3 799469 299801 (by norm_num) (by norm_num) (sr 2 299801 224851 (by norm_num) (by norm_num) (sr 1 224851 337277 (by norm_num) (by norm_num) (sr 3 337277 126479 (by norm_num) (by norm_num) (sr 1 126479 189719 (by norm_num) (by norm_num) (sr 1 189719 284579 (by norm_num) (by norm_num) (sr 1 284579 426869 (by norm_num) (by norm_num) (sr 5 426869 40019 (by norm_num) (by norm_num) (B 40019 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R105283 : Reach 105283 := (sr 1 105283 157925 (by norm_num) (by norm_num) (sr 4 157925 29611 (by norm_num) (by norm_num) (B 29611 (by norm_num) (by norm_num) (by norm_num))))
theorem R105287 : Reach 105287 := (sr 1 105287 157931 (by norm_num) (by norm_num) (sr 1 157931 236897 (by norm_num) (by norm_num) (sr 2 236897 177673 (by norm_num) (by norm_num) (sr 2 177673 133255 (by norm_num) (by norm_num) (sr 1 133255 199883 (by norm_num) (by norm_num) (sr 1 199883 299825 (by norm_num) (by norm_num) (sr 2 299825 224869 (by norm_num) (by norm_num) (sr 4 224869 42163 (by norm_num) (by norm_num) (B 42163 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R105291 : Reach 105291 := (sr 1 105291 157937 (by norm_num) (by norm_num) (sr 2 157937 118453 (by norm_num) (by norm_num) (sr 5 118453 11105 (by norm_num) (by norm_num) (B 11105 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105295 : Reach 105295 := (sr 1 105295 157943 (by norm_num) (by norm_num) (sr 1 157943 236915 (by norm_num) (by norm_num) (sr 1 236915 355373 (by norm_num) (by norm_num) (sr 3 355373 133265 (by norm_num) (by norm_num) (sr 2 133265 99949 (by norm_num) (by norm_num) (sr 3 99949 37481 (by norm_num) (by norm_num) (B 37481 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105299 : Reach 105299 := (sr 1 105299 157949 (by norm_num) (by norm_num) (sr 3 157949 59231 (by norm_num) (by norm_num) (B 59231 (by norm_num) (by norm_num) (by norm_num))))
theorem R105303 : Reach 105303 := (sr 1 105303 157955 (by norm_num) (by norm_num) (sr 1 157955 236933 (by norm_num) (by norm_num) (sr 4 236933 44425 (by norm_num) (by norm_num) (B 44425 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105307 : Reach 105307 := (sr 1 105307 157961 (by norm_num) (by norm_num) (sr 2 157961 118471 (by norm_num) (by norm_num) (sr 1 118471 177707 (by norm_num) (by norm_num) (sr 1 177707 266561 (by norm_num) (by norm_num) (sr 2 266561 199921 (by norm_num) (by norm_num) (sr 2 199921 149941 (by norm_num) (by norm_num) (sr 5 149941 14057 (by norm_num) (by norm_num) (B 14057 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R105311 : Reach 105311 := (sr 1 105311 157967 (by norm_num) (by norm_num) (sr 1 157967 236951 (by norm_num) (by norm_num) (sr 1 236951 355427 (by norm_num) (by norm_num) (sr 1 355427 533141 (by norm_num) (by norm_num) (sr 6 533141 24991 (by norm_num) (by norm_num) (B 24991 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R105315 : Reach 105315 := (sr 1 105315 157973 (by norm_num) (by norm_num) (sr 6 157973 7405 (by norm_num) (by norm_num) (B 7405 (by norm_num) (by norm_num) (by norm_num))))
theorem R105319 : Reach 105319 := (sr 1 105319 157979 (by norm_num) (by norm_num) (sr 1 157979 236969 (by norm_num) (by norm_num) (sr 2 236969 177727 (by norm_num) (by norm_num) (sr 1 177727 266591 (by norm_num) (by norm_num) (sr 1 266591 399887 (by norm_num) (by norm_num) (sr 1 399887 599831 (by norm_num) (by norm_num) (sr 1 599831 899747 (by norm_num) (by norm_num) (sr 1 899747 1349621 (by norm_num) (by norm_num) (sr 5 1349621 126527 (by norm_num) (by norm_num) (sr 1 126527 189791 (by norm_num) (by norm_num) (sr 1 189791 284687 (by norm_num) (by norm_num) (sr 1 284687 427031 (by norm_num) (by norm_num) (sr 1 427031 640547 (by norm_num) (by norm_num) (sr 1 640547 960821 (by norm_num) (by norm_num) (sr 5 960821 90077 (by norm_num) (by norm_num) (B 90077 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R105323 : Reach 105323 := (sr 1 105323 157985 (by norm_num) (by norm_num) (sr 2 157985 118489 (by norm_num) (by norm_num) (sr 2 118489 88867 (by norm_num) (by norm_num) (B 88867 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105327 : Reach 105327 := (sr 1 105327 157991 (by norm_num) (by norm_num) (sr 1 157991 236987 (by norm_num) (by norm_num) (sr 1 236987 355481 (by norm_num) (by norm_num) (sr 2 355481 266611 (by norm_num) (by norm_num) (sr 1 266611 399917 (by norm_num) (by norm_num) (sr 3 399917 149969 (by norm_num) (by norm_num) (sr 2 149969 112477 (by norm_num) (by norm_num) (sr 3 112477 42179 (by norm_num) (by norm_num) (B 42179 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R105331 : Reach 105331 := (sr 1 105331 157997 (by norm_num) (by norm_num) (sr 3 157997 59249 (by norm_num) (by norm_num) (B 59249 (by norm_num) (by norm_num) (by norm_num))))
theorem R105335 : Reach 105335 := (sr 1 105335 158003 (by norm_num) (by norm_num) (sr 1 158003 237005 (by norm_num) (by norm_num) (sr 3 237005 88877 (by norm_num) (by norm_num) (B 88877 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105339 : Reach 105339 := (sr 1 105339 158009 (by norm_num) (by norm_num) (sr 2 158009 118507 (by norm_num) (by norm_num) (sr 1 118507 177761 (by norm_num) (by norm_num) (sr 2 177761 133321 (by norm_num) (by norm_num) (sr 2 133321 99991 (by norm_num) (by norm_num) R99991)))))
theorem R105343 : Reach 105343 := (sr 1 105343 158015 (by norm_num) (by norm_num) (sr 1 158015 237023 (by norm_num) (by norm_num) (sr 1 237023 355535 (by norm_num) (by norm_num) (sr 1 355535 533303 (by norm_num) (by norm_num) (sr 1 533303 799955 (by norm_num) (by norm_num) (sr 1 799955 1199933 (by norm_num) (by norm_num) (sr 3 1199933 449975 (by norm_num) (by norm_num) (sr 1 449975 674963 (by norm_num) (by norm_num) (sr 1 674963 1012445 (by norm_num) (by norm_num) (sr 3 1012445 379667 (by norm_num) (by norm_num) (sr 1 379667 569501 (by norm_num) (by norm_num) (sr 3 569501 213563 (by norm_num) (by norm_num) (sr 1 213563 320345 (by norm_num) (by norm_num) (sr 2 320345 240259 (by norm_num) (by norm_num) (sr 1 240259 360389 (by norm_num) (by norm_num) (sr 4 360389 67573 (by norm_num) (by norm_num) (B 67573 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))
theorem R105347 : Reach 105347 := (sr 1 105347 158021 (by norm_num) (by norm_num) (sr 4 158021 29629 (by norm_num) (by norm_num) (B 29629 (by norm_num) (by norm_num) (by norm_num))))
theorem R105351 : Reach 105351 := (sr 1 105351 158027 (by norm_num) (by norm_num) (sr 1 158027 237041 (by norm_num) (by norm_num) (sr 2 237041 177781 (by norm_num) (by norm_num) (sr 5 177781 16667 (by norm_num) (by norm_num) (B 16667 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105355 : Reach 105355 := (sr 1 105355 158033 (by norm_num) (by norm_num) (sr 2 158033 118525 (by norm_num) (by norm_num) (sr 3 118525 44447 (by norm_num) (by norm_num) (B 44447 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105359 : Reach 105359 := (sr 1 105359 158039 (by norm_num) (by norm_num) (sr 1 158039 237059 (by norm_num) (by norm_num) (sr 1 237059 355589 (by norm_num) (by norm_num) (sr 4 355589 66673 (by norm_num) (by norm_num) (B 66673 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105363 : Reach 105363 := (sr 1 105363 158045 (by norm_num) (by norm_num) (sr 3 158045 59267 (by norm_num) (by norm_num) (B 59267 (by norm_num) (by norm_num) (by norm_num))))
theorem R105367 : Reach 105367 := (sr 1 105367 158051 (by norm_num) (by norm_num) (sr 1 158051 237077 (by norm_num) (by norm_num) (sr 6 237077 11113 (by norm_num) (by norm_num) (B 11113 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105371 : Reach 105371 := (sr 1 105371 158057 (by norm_num) (by norm_num) (sr 2 158057 118543 (by norm_num) (by norm_num) (sr 1 118543 177815 (by norm_num) (by norm_num) (sr 1 177815 266723 (by norm_num) (by norm_num) (sr 1 266723 400085 (by norm_num) (by norm_num) (sr 7 400085 9377 (by norm_num) (by norm_num) (B 9377 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105375 : Reach 105375 := (sr 1 105375 158063 (by norm_num) (by norm_num) (sr 1 158063 237095 (by norm_num) (by norm_num) (sr 1 237095 355643 (by norm_num) (by norm_num) (sr 1 355643 533465 (by norm_num) (by norm_num) (sr 2 533465 400099 (by norm_num) (by norm_num) (sr 1 400099 600149 (by norm_num) (by norm_num) (sr 8 600149 7033 (by norm_num) (by norm_num) (B 7033 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R105379 : Reach 105379 := (sr 1 105379 158069 (by norm_num) (by norm_num) (sr 5 158069 14819 (by norm_num) (by norm_num) (B 14819 (by norm_num) (by norm_num) (by norm_num))))
theorem R105383 : Reach 105383 := (sr 1 105383 158075 (by norm_num) (by norm_num) (sr 1 158075 237113 (by norm_num) (by norm_num) (sr 2 237113 177835 (by norm_num) (by norm_num) (sr 1 177835 266753 (by norm_num) (by norm_num) (sr 2 266753 200065 (by norm_num) (by norm_num) (sr 2 200065 150049 (by norm_num) (by norm_num) (sr 2 150049 112537 (by norm_num) (by norm_num) (sr 2 112537 84403 (by norm_num) (by norm_num) (B 84403 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R105387 : Reach 105387 := (sr 1 105387 158081 (by norm_num) (by norm_num) (sr 2 158081 118561 (by norm_num) (by norm_num) (sr 2 118561 88921 (by norm_num) (by norm_num) (B 88921 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105391 : Reach 105391 := (sr 1 105391 158087 (by norm_num) (by norm_num) (sr 1 158087 237131 (by norm_num) (by norm_num) (sr 1 237131 355697 (by norm_num) (by norm_num) (sr 2 355697 266773 (by norm_num) (by norm_num) (sr 6 266773 12505 (by norm_num) (by norm_num) (B 12505 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R105395 : Reach 105395 := (sr 1 105395 158093 (by norm_num) (by norm_num) (sr 3 158093 59285 (by norm_num) (by norm_num) (B 59285 (by norm_num) (by norm_num) (by norm_num))))
theorem R105399 : Reach 105399 := (sr 1 105399 158099 (by norm_num) (by norm_num) (sr 1 158099 237149 (by norm_num) (by norm_num) (sr 3 237149 88931 (by norm_num) (by norm_num) (B 88931 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105403 : Reach 105403 := (sr 1 105403 158105 (by norm_num) (by norm_num) (sr 2 158105 118579 (by norm_num) (by norm_num) (sr 1 118579 177869 (by norm_num) (by norm_num) (sr 3 177869 66701 (by norm_num) (by norm_num) (B 66701 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105407 : Reach 105407 := (sr 1 105407 158111 (by norm_num) (by norm_num) (sr 1 158111 237167 (by norm_num) (by norm_num) (sr 1 237167 355751 (by norm_num) (by norm_num) (sr 1 355751 533627 (by norm_num) (by norm_num) (sr 1 533627 800441 (by norm_num) (by norm_num) (sr 2 800441 600331 (by norm_num) (by norm_num) (sr 1 600331 900497 (by norm_num) (by norm_num) (sr 2 900497 675373 (by norm_num) (by norm_num) (sr 3 675373 253265 (by norm_num) (by norm_num) (sr 2 253265 189949 (by norm_num) (by norm_num) (sr 3 189949 71231 (by norm_num) (by norm_num) (B 71231 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R105411 : Reach 105411 := (sr 1 105411 158117 (by norm_num) (by norm_num) (sr 4 158117 29647 (by norm_num) (by norm_num) (B 29647 (by norm_num) (by norm_num) (by norm_num))))
theorem R105415 : Reach 105415 := (sr 1 105415 158123 (by norm_num) (by norm_num) (sr 1 158123 237185 (by norm_num) (by norm_num) (sr 2 237185 177889 (by norm_num) (by norm_num) (sr 2 177889 133417 (by norm_num) (by norm_num) (sr 2 133417 100063 (by norm_num) (by norm_num) R100063)))))
theorem R105419 : Reach 105419 := (sr 1 105419 158129 (by norm_num) (by norm_num) (sr 2 158129 118597 (by norm_num) (by norm_num) (sr 4 118597 22237 (by norm_num) (by norm_num) (B 22237 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105423 : Reach 105423 := (sr 1 105423 158135 (by norm_num) (by norm_num) (sr 1 158135 237203 (by norm_num) (by norm_num) (sr 1 237203 355805 (by norm_num) (by norm_num) (sr 3 355805 133427 (by norm_num) (by norm_num) (sr 1 133427 200141 (by norm_num) (by norm_num) (sr 3 200141 75053 (by norm_num) (by norm_num) (B 75053 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105427 : Reach 105427 := (sr 1 105427 158141 (by norm_num) (by norm_num) (sr 3 158141 59303 (by norm_num) (by norm_num) (B 59303 (by norm_num) (by norm_num) (by norm_num))))
theorem R105431 : Reach 105431 := (sr 1 105431 158147 (by norm_num) (by norm_num) (sr 1 158147 237221 (by norm_num) (by norm_num) (sr 4 237221 44479 (by norm_num) (by norm_num) (B 44479 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105435 : Reach 105435 := (sr 1 105435 158153 (by norm_num) (by norm_num) (sr 2 158153 118615 (by norm_num) (by norm_num) (sr 1 118615 177923 (by norm_num) (by norm_num) (sr 1 177923 266885 (by norm_num) (by norm_num) (sr 4 266885 50041 (by norm_num) (by norm_num) (B 50041 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R105439 : Reach 105439 := (sr 1 105439 158159 (by norm_num) (by norm_num) (sr 1 158159 237239 (by norm_num) (by norm_num) (sr 1 237239 355859 (by norm_num) (by norm_num) (sr 1 355859 533789 (by norm_num) (by norm_num) (sr 3 533789 200171 (by norm_num) (by norm_num) (sr 1 200171 300257 (by norm_num) (by norm_num) (sr 2 300257 225193 (by norm_num) (by norm_num) (sr 2 225193 168895 (by norm_num) (by norm_num) (sr 1 168895 253343 (by norm_num) (by norm_num) (sr 1 253343 380015 (by norm_num) (by norm_num) (sr 1 380015 570023 (by norm_num) (by norm_num) (sr 1 570023 855035 (by norm_num) (by norm_num) (sr 1 855035 1282553 (by norm_num) (by norm_num) (sr 2 1282553 961915 (by norm_num) (by norm_num) (sr 1 961915 1442873 (by norm_num) (by norm_num) (sr 2 1442873 1082155 (by norm_num) (by norm_num) (sr 1 1082155 1623233 (by norm_num) (by norm_num) (sr 2 1623233 1217425 (by norm_num) (by norm_num) (sr 2 1217425 913069 (by norm_num) (by norm_num) (sr 3 913069 342401 (by norm_num) (by norm_num) (sr 2 342401 256801 (by norm_num) (by norm_num) (sr 2 256801 192601 (by norm_num) (by norm_num) (sr 2 192601 144451 (by norm_num) (by norm_num) (sr 1 144451 216677 (by norm_num) (by norm_num) (sr 4 216677 40627 (by norm_num) (by norm_num) (B 40627 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))
theorem R105443 : Reach 105443 := (sr 1 105443 158165 (by norm_num) (by norm_num) (sr 7 158165 3707 (by norm_num) (by norm_num) (B 3707 (by norm_num) (by norm_num) (by norm_num))))
theorem R105447 : Reach 105447 := (sr 1 105447 158171 (by norm_num) (by norm_num) (sr 1 158171 237257 (by norm_num) (by norm_num) (sr 2 237257 177943 (by norm_num) (by norm_num) (sr 1 177943 266915 (by norm_num) (by norm_num) (sr 1 266915 400373 (by norm_num) (by norm_num) (sr 5 400373 37535 (by norm_num) (by norm_num) (B 37535 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105451 : Reach 105451 := (sr 1 105451 158177 (by norm_num) (by norm_num) (sr 2 158177 118633 (by norm_num) (by norm_num) (sr 2 118633 88975 (by norm_num) (by norm_num) (B 88975 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105455 : Reach 105455 := (sr 1 105455 158183 (by norm_num) (by norm_num) (sr 1 158183 237275 (by norm_num) (by norm_num) (sr 1 237275 355913 (by norm_num) (by norm_num) (sr 2 355913 266935 (by norm_num) (by norm_num) (sr 1 266935 400403 (by norm_num) (by norm_num) (sr 1 400403 600605 (by norm_num) (by norm_num) (sr 3 600605 225227 (by norm_num) (by norm_num) (sr 1 225227 337841 (by norm_num) (by norm_num) (sr 2 337841 253381 (by norm_num) (by norm_num) (sr 4 253381 47509 (by norm_num) (by norm_num) (B 47509 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R105459 : Reach 105459 := (sr 1 105459 158189 (by norm_num) (by norm_num) (sr 3 158189 59321 (by norm_num) (by norm_num) (B 59321 (by norm_num) (by norm_num) (by norm_num))))
theorem R105463 : Reach 105463 := (sr 1 105463 158195 (by norm_num) (by norm_num) (sr 1 158195 237293 (by norm_num) (by norm_num) (sr 3 237293 88985 (by norm_num) (by norm_num) (B 88985 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105467 : Reach 105467 := (sr 1 105467 158201 (by norm_num) (by norm_num) (sr 2 158201 118651 (by norm_num) (by norm_num) (sr 1 118651 177977 (by norm_num) (by norm_num) (sr 2 177977 133483 (by norm_num) (by norm_num) (sr 1 133483 200225 (by norm_num) (by norm_num) (sr 2 200225 150169 (by norm_num) (by norm_num) (sr 2 150169 112627 (by norm_num) (by norm_num) (sr 1 112627 168941 (by norm_num) (by norm_num) (sr 3 168941 63353 (by norm_num) (by norm_num) (B 63353 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R105471 : Reach 105471 := (sr 1 105471 158207 (by norm_num) (by norm_num) (sr 1 158207 237311 (by norm_num) (by norm_num) (sr 1 237311 355967 (by norm_num) (by norm_num) (sr 1 355967 533951 (by norm_num) (by norm_num) (sr 1 533951 800927 (by norm_num) (by norm_num) (sr 1 800927 1201391 (by norm_num) (by norm_num) (sr 1 1201391 1802087 (by norm_num) (by norm_num) (sr 1 1802087 2703131 (by norm_num) (by norm_num) (sr 1 2703131 4054697 (by norm_num) (by norm_num) (sr 2 4054697 3041023 (by norm_num) (by norm_num) (sr 1 3041023 4561535 (by norm_num) (by norm_num) (sr 1 4561535 6842303 (by norm_num) (by norm_num) (sr 1 6842303 10263455 (by norm_num) (by norm_num) (sr 1 10263455 15395183 (by norm_num) (by norm_num) (sr 1 15395183 23092775 (by norm_num) (by norm_num) (sr 1 23092775 34639163 (by norm_num) (by norm_num) (sr 1 34639163 51958745 (by norm_num) (by norm_num) (sr 2 51958745 38969059 (by norm_num) (by norm_num) (sr 1 38969059 58453589 (by norm_num) (by norm_num) (sr 8 58453589 685003 (by norm_num) (by norm_num) (sr 1 685003 1027505 (by norm_num) (by norm_num) (sr 2 1027505 770629 (by norm_num) (by norm_num) (sr 4 770629 144493 (by norm_num) (by norm_num) (sr 3 144493 54185 (by norm_num) (by norm_num) (B 54185 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))
theorem R105475 : Reach 105475 := (sr 1 105475 158213 (by norm_num) (by norm_num) (sr 4 158213 29665 (by norm_num) (by norm_num) (B 29665 (by norm_num) (by norm_num) (by norm_num))))
theorem R105479 : Reach 105479 := (sr 1 105479 158219 (by norm_num) (by norm_num) (sr 1 158219 237329 (by norm_num) (by norm_num) (sr 2 237329 177997 (by norm_num) (by norm_num) (sr 3 177997 66749 (by norm_num) (by norm_num) (B 66749 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105483 : Reach 105483 := (sr 1 105483 158225 (by norm_num) (by norm_num) (sr 2 158225 118669 (by norm_num) (by norm_num) (sr 3 118669 44501 (by norm_num) (by norm_num) (B 44501 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105487 : Reach 105487 := (sr 1 105487 158231 (by norm_num) (by norm_num) (sr 1 158231 237347 (by norm_num) (by norm_num) (sr 1 237347 356021 (by norm_num) (by norm_num) (sr 5 356021 33377 (by norm_num) (by norm_num) (B 33377 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105491 : Reach 105491 := (sr 1 105491 158237 (by norm_num) (by norm_num) (sr 3 158237 59339 (by norm_num) (by norm_num) (B 59339 (by norm_num) (by norm_num) (by norm_num))))
theorem R105495 : Reach 105495 := (sr 1 105495 158243 (by norm_num) (by norm_num) (sr 1 158243 237365 (by norm_num) (by norm_num) (sr 5 237365 22253 (by norm_num) (by norm_num) (B 22253 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105499 : Reach 105499 := (sr 1 105499 158249 (by norm_num) (by norm_num) (sr 2 158249 118687 (by norm_num) (by norm_num) (sr 1 118687 178031 (by norm_num) (by norm_num) (sr 1 178031 267047 (by norm_num) (by norm_num) (sr 1 267047 400571 (by norm_num) (by norm_num) (sr 1 400571 600857 (by norm_num) (by norm_num) (sr 2 600857 450643 (by norm_num) (by norm_num) (sr 1 450643 675965 (by norm_num) (by norm_num) (sr 3 675965 253487 (by norm_num) (by norm_num) (sr 1 253487 380231 (by norm_num) (by norm_num) (sr 1 380231 570347 (by norm_num) (by norm_num) (sr 1 570347 855521 (by norm_num) (by norm_num) (sr 2 855521 641641 (by norm_num) (by norm_num) (sr 2 641641 481231 (by norm_num) (by norm_num) (sr 1 481231 721847 (by norm_num) (by norm_num) (sr 1 721847 1082771 (by norm_num) (by norm_num) (sr 1 1082771 1624157 (by norm_num) (by norm_num) (sr 3 1624157 609059 (by norm_num) (by norm_num) (sr 1 609059 913589 (by norm_num) (by norm_num) (sr 5 913589 85649 (by norm_num) (by norm_num) (B 85649 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))
theorem R105503 : Reach 105503 := (sr 1 105503 158255 (by norm_num) (by norm_num) (sr 1 158255 237383 (by norm_num) (by norm_num) (sr 1 237383 356075 (by norm_num) (by norm_num) (sr 1 356075 534113 (by norm_num) (by norm_num) (sr 2 534113 400585 (by norm_num) (by norm_num) (sr 2 400585 300439 (by norm_num) (by norm_num) (sr 1 300439 450659 (by norm_num) (by norm_num) (sr 1 450659 675989 (by norm_num) (by norm_num) (sr 6 675989 31687 (by norm_num) (by norm_num) (B 31687 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R105507 : Reach 105507 := (sr 1 105507 158261 (by norm_num) (by norm_num) (sr 5 158261 14837 (by norm_num) (by norm_num) (B 14837 (by norm_num) (by norm_num) (by norm_num))))
theorem R105511 : Reach 105511 := (sr 1 105511 158267 (by norm_num) (by norm_num) (sr 1 158267 237401 (by norm_num) (by norm_num) (sr 2 237401 178051 (by norm_num) (by norm_num) (sr 1 178051 267077 (by norm_num) (by norm_num) (sr 4 267077 50077 (by norm_num) (by norm_num) (B 50077 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R105515 : Reach 105515 := (sr 1 105515 158273 (by norm_num) (by norm_num) (sr 2 158273 118705 (by norm_num) (by norm_num) (sr 2 118705 89029 (by norm_num) (by norm_num) (B 89029 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105519 : Reach 105519 := (sr 1 105519 158279 (by norm_num) (by norm_num) (sr 1 158279 237419 (by norm_num) (by norm_num) (sr 1 237419 356129 (by norm_num) (by norm_num) (sr 2 356129 267097 (by norm_num) (by norm_num) (sr 2 267097 200323 (by norm_num) (by norm_num) (sr 1 200323 300485 (by norm_num) (by norm_num) (sr 4 300485 56341 (by norm_num) (by norm_num) (B 56341 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R105523 : Reach 105523 := (sr 1 105523 158285 (by norm_num) (by norm_num) (sr 3 158285 59357 (by norm_num) (by norm_num) (B 59357 (by norm_num) (by norm_num) (by norm_num))))
theorem R105527 : Reach 105527 := (sr 1 105527 158291 (by norm_num) (by norm_num) (sr 1 158291 237437 (by norm_num) (by norm_num) (sr 3 237437 89039 (by norm_num) (by norm_num) (B 89039 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105531 : Reach 105531 := (sr 1 105531 158297 (by norm_num) (by norm_num) (sr 2 158297 118723 (by norm_num) (by norm_num) (sr 1 118723 178085 (by norm_num) (by norm_num) (sr 4 178085 33391 (by norm_num) (by norm_num) (B 33391 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105535 : Reach 105535 := (sr 1 105535 158303 (by norm_num) (by norm_num) (sr 1 158303 237455 (by norm_num) (by norm_num) (sr 1 237455 356183 (by norm_num) (by norm_num) (sr 1 356183 534275 (by norm_num) (by norm_num) (sr 1 534275 801413 (by norm_num) (by norm_num) (sr 4 801413 150265 (by norm_num) (by norm_num) (sr 2 150265 112699 (by norm_num) (by norm_num) (sr 1 112699 169049 (by norm_num) (by norm_num) (sr 2 169049 126787 (by norm_num) (by norm_num) (sr 1 126787 190181 (by norm_num) (by norm_num) (sr 4 190181 35659 (by norm_num) (by norm_num) (B 35659 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R105539 : Reach 105539 := (sr 1 105539 158309 (by norm_num) (by norm_num) (sr 4 158309 29683 (by norm_num) (by norm_num) (B 29683 (by norm_num) (by norm_num) (by norm_num))))
theorem R105543 : Reach 105543 := (sr 1 105543 158315 (by norm_num) (by norm_num) (sr 1 158315 237473 (by norm_num) (by norm_num) (sr 2 237473 178105 (by norm_num) (by norm_num) (sr 2 178105 133579 (by norm_num) (by norm_num) (sr 1 133579 200369 (by norm_num) (by norm_num) (sr 2 200369 150277 (by norm_num) (by norm_num) (sr 4 150277 28177 (by norm_num) (by norm_num) (B 28177 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R105547 : Reach 105547 := (sr 1 105547 158321 (by norm_num) (by norm_num) (sr 2 158321 118741 (by norm_num) (by norm_num) (sr 7 118741 2783 (by norm_num) (by norm_num) (B 2783 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105551 : Reach 105551 := (sr 1 105551 158327 (by norm_num) (by norm_num) (sr 1 158327 237491 (by norm_num) (by norm_num) (sr 1 237491 356237 (by norm_num) (by norm_num) (sr 3 356237 133589 (by norm_num) (by norm_num) (sr 7 133589 3131 (by norm_num) (by norm_num) (B 3131 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R105555 : Reach 105555 := (sr 1 105555 158333 (by norm_num) (by norm_num) (sr 3 158333 59375 (by norm_num) (by norm_num) (B 59375 (by norm_num) (by norm_num) (by norm_num))))
theorem R105559 : Reach 105559 := (sr 1 105559 158339 (by norm_num) (by norm_num) (sr 1 158339 237509 (by norm_num) (by norm_num) (sr 4 237509 44533 (by norm_num) (by norm_num) (B 44533 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105563 : Reach 105563 := (sr 1 105563 158345 (by norm_num) (by norm_num) (sr 2 158345 118759 (by norm_num) (by norm_num) (sr 1 118759 178139 (by norm_num) (by norm_num) (sr 1 178139 267209 (by norm_num) (by norm_num) (sr 2 267209 200407 (by norm_num) (by norm_num) (sr 1 200407 300611 (by norm_num) (by norm_num) (sr 1 300611 450917 (by norm_num) (by norm_num) (sr 4 450917 84547 (by norm_num) (by norm_num) (B 84547 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R105567 : Reach 105567 := (sr 1 105567 158351 (by norm_num) (by norm_num) (sr 1 158351 237527 (by norm_num) (by norm_num) (sr 1 237527 356291 (by norm_num) (by norm_num) (sr 1 356291 534437 (by norm_num) (by norm_num) (sr 4 534437 100207 (by norm_num) (by norm_num) R100207)))))
theorem R105571 : Reach 105571 := (sr 1 105571 158357 (by norm_num) (by norm_num) (sr 6 158357 7423 (by norm_num) (by norm_num) (B 7423 (by norm_num) (by norm_num) (by norm_num))))
theorem R105575 : Reach 105575 := (sr 1 105575 158363 (by norm_num) (by norm_num) (sr 1 158363 237545 (by norm_num) (by norm_num) (sr 2 237545 178159 (by norm_num) (by norm_num) (sr 1 178159 267239 (by norm_num) (by norm_num) (sr 1 267239 400859 (by norm_num) (by norm_num) (sr 1 400859 601289 (by norm_num) (by norm_num) (sr 2 601289 450967 (by norm_num) (by norm_num) (sr 1 450967 676451 (by norm_num) (by norm_num) (sr 1 676451 1014677 (by norm_num) (by norm_num) (sr 6 1014677 47563 (by norm_num) (by norm_num) (B 47563 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R105579 : Reach 105579 := (sr 1 105579 158369 (by norm_num) (by norm_num) (sr 2 158369 118777 (by norm_num) (by norm_num) (sr 2 118777 89083 (by norm_num) (by norm_num) (B 89083 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105583 : Reach 105583 := (sr 1 105583 158375 (by norm_num) (by norm_num) (sr 1 158375 237563 (by norm_num) (by norm_num) (sr 1 237563 356345 (by norm_num) (by norm_num) (sr 2 356345 267259 (by norm_num) (by norm_num) (sr 1 267259 400889 (by norm_num) (by norm_num) (sr 2 400889 300667 (by norm_num) (by norm_num) (sr 1 300667 451001 (by norm_num) (by norm_num) (sr 2 451001 338251 (by norm_num) (by norm_num) (sr 1 338251 507377 (by norm_num) (by norm_num) (sr 2 507377 380533 (by norm_num) (by norm_num) (sr 5 380533 35675 (by norm_num) (by norm_num) (B 35675 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R105587 : Reach 105587 := (sr 1 105587 158381 (by norm_num) (by norm_num) (sr 3 158381 59393 (by norm_num) (by norm_num) (B 59393 (by norm_num) (by norm_num) (by norm_num))))
theorem R105591 : Reach 105591 := (sr 1 105591 158387 (by norm_num) (by norm_num) (sr 1 158387 237581 (by norm_num) (by norm_num) (sr 3 237581 89093 (by norm_num) (by norm_num) (B 89093 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105595 : Reach 105595 := (sr 1 105595 158393 (by norm_num) (by norm_num) (sr 2 158393 118795 (by norm_num) (by norm_num) (sr 1 118795 178193 (by norm_num) (by norm_num) (sr 2 178193 133645 (by norm_num) (by norm_num) (sr 3 133645 50117 (by norm_num) (by norm_num) (B 50117 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R105599 : Reach 105599 := (sr 1 105599 158399 (by norm_num) (by norm_num) (sr 1 158399 237599 (by norm_num) (by norm_num) (sr 1 237599 356399 (by norm_num) (by norm_num) (sr 1 356399 534599 (by norm_num) (by norm_num) (sr 1 534599 801899 (by norm_num) (by norm_num) (sr 1 801899 1202849 (by norm_num) (by norm_num) (sr 2 1202849 902137 (by norm_num) (by norm_num) (sr 2 902137 676603 (by norm_num) (by norm_num) (sr 1 676603 1014905 (by norm_num) (by norm_num) (sr 2 1014905 761179 (by norm_num) (by norm_num) (sr 1 761179 1141769 (by norm_num) (by norm_num) (sr 2 1141769 856327 (by norm_num) (by norm_num) (sr 1 856327 1284491 (by norm_num) (by norm_num) (sr 1 1284491 1926737 (by norm_num) (by norm_num) (sr 2 1926737 1445053 (by norm_num) (by norm_num) (sr 3 1445053 541895 (by norm_num) (by norm_num) (sr 1 541895 812843 (by norm_num) (by norm_num) (sr 1 812843 1219265 (by norm_num) (by norm_num) (sr 2 1219265 914449 (by norm_num) (by norm_num) (sr 2 914449 685837 (by norm_num) (by norm_num) (sr 3 685837 257189 (by norm_num) (by norm_num) (sr 4 257189 48223 (by norm_num) (by norm_num) (B 48223 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R105603 : Reach 105603 := (sr 1 105603 158405 (by norm_num) (by norm_num) (sr 4 158405 29701 (by norm_num) (by norm_num) (B 29701 (by norm_num) (by norm_num) (by norm_num))))
theorem R105607 : Reach 105607 := (sr 1 105607 158411 (by norm_num) (by norm_num) (sr 1 158411 237617 (by norm_num) (by norm_num) (sr 2 237617 178213 (by norm_num) (by norm_num) (sr 4 178213 33415 (by norm_num) (by norm_num) (B 33415 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105611 : Reach 105611 := (sr 1 105611 158417 (by norm_num) (by norm_num) (sr 2 158417 118813 (by norm_num) (by norm_num) (sr 3 118813 44555 (by norm_num) (by norm_num) (B 44555 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105615 : Reach 105615 := (sr 1 105615 158423 (by norm_num) (by norm_num) (sr 1 158423 237635 (by norm_num) (by norm_num) (sr 1 237635 356453 (by norm_num) (by norm_num) (sr 4 356453 66835 (by norm_num) (by norm_num) (B 66835 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105619 : Reach 105619 := (sr 1 105619 158429 (by norm_num) (by norm_num) (sr 3 158429 59411 (by norm_num) (by norm_num) (B 59411 (by norm_num) (by norm_num) (by norm_num))))
theorem R105623 : Reach 105623 := (sr 1 105623 158435 (by norm_num) (by norm_num) (sr 1 158435 237653 (by norm_num) (by norm_num) (sr 8 237653 2785 (by norm_num) (by norm_num) (B 2785 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105627 : Reach 105627 := (sr 1 105627 158441 (by norm_num) (by norm_num) (sr 2 158441 118831 (by norm_num) (by norm_num) (sr 1 118831 178247 (by norm_num) (by norm_num) (sr 1 178247 267371 (by norm_num) (by norm_num) (sr 1 267371 401057 (by norm_num) (by norm_num) (sr 2 401057 300793 (by norm_num) (by norm_num) (sr 2 300793 225595 (by norm_num) (by norm_num) (sr 1 225595 338393 (by norm_num) (by norm_num) (sr 2 338393 253795 (by norm_num) (by norm_num) (sr 1 253795 380693 (by norm_num) (by norm_num) (sr 6 380693 17845 (by norm_num) (by norm_num) (B 17845 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R105631 : Reach 105631 := (sr 1 105631 158447 (by norm_num) (by norm_num) (sr 1 158447 237671 (by norm_num) (by norm_num) (sr 1 237671 356507 (by norm_num) (by norm_num) (sr 1 356507 534761 (by norm_num) (by norm_num) (sr 2 534761 401071 (by norm_num) (by norm_num) (sr 1 401071 601607 (by norm_num) (by norm_num) (sr 1 601607 902411 (by norm_num) (by norm_num) (sr 1 902411 1353617 (by norm_num) (by norm_num) (sr 2 1353617 1015213 (by norm_num) (by norm_num) (sr 3 1015213 380705 (by norm_num) (by norm_num) (sr 2 380705 285529 (by norm_num) (by norm_num) (sr 2 285529 214147 (by norm_num) (by norm_num) (sr 1 214147 321221 (by norm_num) (by norm_num) (sr 4 321221 60229 (by norm_num) (by norm_num) (B 60229 (by norm_num) (by norm_num) (by norm_num))))))))))))))))
theorem R105635 : Reach 105635 := (sr 1 105635 158453 (by norm_num) (by norm_num) (sr 5 158453 14855 (by norm_num) (by norm_num) (B 14855 (by norm_num) (by norm_num) (by norm_num))))
theorem R105639 : Reach 105639 := (sr 1 105639 158459 (by norm_num) (by norm_num) (sr 1 158459 237689 (by norm_num) (by norm_num) (sr 2 237689 178267 (by norm_num) (by norm_num) (sr 1 178267 267401 (by norm_num) (by norm_num) (sr 2 267401 200551 (by norm_num) (by norm_num) (sr 1 200551 300827 (by norm_num) (by norm_num) (sr 1 300827 451241 (by norm_num) (by norm_num) (sr 2 451241 338431 (by norm_num) (by norm_num) (sr 1 338431 507647 (by norm_num) (by norm_num) (sr 1 507647 761471 (by norm_num) (by norm_num) (sr 1 761471 1142207 (by norm_num) (by norm_num) (sr 1 1142207 1713311 (by norm_num) (by norm_num) (sr 1 1713311 2569967 (by norm_num) (by norm_num) (sr 1 2569967 3854951 (by norm_num) (by norm_num) (sr 1 3854951 5782427 (by norm_num) (by norm_num) (sr 1 5782427 8673641 (by norm_num) (by norm_num) (sr 2 8673641 6505231 (by norm_num) (by norm_num) (sr 1 6505231 9757847 (by norm_num) (by norm_num) (sr 1 9757847 14636771 (by norm_num) (by norm_num) (sr 1 14636771 21955157 (by norm_num) (by norm_num) (sr 8 21955157 257287 (by norm_num) (by norm_num) (sr 1 257287 385931 (by norm_num) (by norm_num) (sr 1 385931 578897 (by norm_num) (by norm_num) (sr 2 578897 434173 (by norm_num) (by norm_num) (sr 3 434173 162815 (by norm_num) (by norm_num) (sr 1 162815 244223 (by norm_num) (by norm_num) (sr 1 244223 366335 (by norm_num) (by norm_num) (sr 1 366335 549503 (by norm_num) (by norm_num) (sr 1 549503 824255 (by norm_num) (by norm_num) (sr 1 824255 1236383 (by norm_num) (by norm_num) (sr 1 1236383 1854575 (by norm_num) (by norm_num) (sr 1 1854575 2781863 (by norm_num) (by norm_num) (sr 1 2781863 4172795 (by norm_num) (by norm_num) (sr 1 4172795 6259193 (by norm_num) (by norm_num) (sr 2 6259193 4694395 (by norm_num) (by norm_num) (sr 1 4694395 7041593 (by norm_num) (by norm_num) (sr 2 7041593 5281195 (by norm_num) (by norm_num) (sr 1 5281195 7921793 (by norm_num) (by norm_num) (sr 2 7921793 5941345 (by norm_num) (by norm_num) (sr 2 5941345 4456009 (by norm_num) (by norm_num) (sr 2 4456009 3342007 (by norm_num) (by norm_num) (sr 1 3342007 5013011 (by norm_num) (by norm_num) (sr 1 5013011 7519517 (by norm_num) (by norm_num) (sr 3 7519517 2819819 (by norm_num) (by norm_num) (sr 1 2819819 4229729 (by norm_num) (by norm_num) (sr 2 4229729 3172297 (by norm_num) (by norm_num) (sr 2 3172297 2379223 (by norm_num) (by norm_num) (sr 1 2379223 3568835 (by norm_num) (by norm_num) (sr 1 3568835 5353253 (by norm_num) (by norm_num) (sr 4 5353253 1003735 (by norm_num) (by norm_num) (sr 1 1003735 1505603 (by norm_num) (by norm_num) (sr 1 1505603 2258405 (by norm_num) (by norm_num) (sr 4 2258405 423451 (by norm_num) (by norm_num) (sr 1 423451 635177 (by norm_num) (by norm_num) (sr 2 635177 476383 (by norm_num) (by norm_num) (sr 1 476383 714575 (by norm_num) (by norm_num) (sr 1 714575 1071863 (by norm_num) (by norm_num) (sr 1 1071863 1607795 (by norm_num) (by norm_num) (sr 1 1607795 2411693 (by norm_num) (by norm_num) (sr 3 2411693 904385 (by norm_num) (by norm_num) (sr 2 904385 678289 (by norm_num) (by norm_num) (sr 2 678289 508717 (by norm_num) (by norm_num) (sr 3 508717 190769 (by norm_num) (by norm_num) (sr 2 190769 143077 (by norm_num) (by norm_num) (sr 4 143077 26827 (by norm_num) (by norm_num) (B 26827 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem R105643 : Reach 105643 := (sr 1 105643 158465 (by norm_num) (by norm_num) (sr 2 158465 118849 (by norm_num) (by norm_num) (sr 2 118849 89137 (by norm_num) (by norm_num) (B 89137 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105647 : Reach 105647 := (sr 1 105647 158471 (by norm_num) (by norm_num) (sr 1 158471 237707 (by norm_num) (by norm_num) (sr 1 237707 356561 (by norm_num) (by norm_num) (sr 2 356561 267421 (by norm_num) (by norm_num) (sr 3 267421 100283 (by norm_num) (by norm_num) R100283)))))
theorem R105651 : Reach 105651 := (sr 1 105651 158477 (by norm_num) (by norm_num) (sr 3 158477 59429 (by norm_num) (by norm_num) (B 59429 (by norm_num) (by norm_num) (by norm_num))))
theorem R105655 : Reach 105655 := (sr 1 105655 158483 (by norm_num) (by norm_num) (sr 1 158483 237725 (by norm_num) (by norm_num) (sr 3 237725 89147 (by norm_num) (by norm_num) (B 89147 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105659 : Reach 105659 := (sr 1 105659 158489 (by norm_num) (by norm_num) (sr 2 158489 118867 (by norm_num) (by norm_num) (sr 1 118867 178301 (by norm_num) (by norm_num) (sr 3 178301 66863 (by norm_num) (by norm_num) (B 66863 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105663 : Reach 105663 := (sr 1 105663 158495 (by norm_num) (by norm_num) (sr 1 158495 237743 (by norm_num) (by norm_num) (sr 1 237743 356615 (by norm_num) (by norm_num) (sr 1 356615 534923 (by norm_num) (by norm_num) (sr 1 534923 802385 (by norm_num) (by norm_num) (sr 2 802385 601789 (by norm_num) (by norm_num) (sr 3 601789 225671 (by norm_num) (by norm_num) (sr 1 225671 338507 (by norm_num) (by norm_num) (sr 1 338507 507761 (by norm_num) (by norm_num) (sr 2 507761 380821 (by norm_num) (by norm_num) (sr 6 380821 17851 (by norm_num) (by norm_num) (B 17851 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R105667 : Reach 105667 := (sr 1 105667 158501 (by norm_num) (by norm_num) (sr 4 158501 29719 (by norm_num) (by norm_num) (B 29719 (by norm_num) (by norm_num) (by norm_num))))
theorem R105671 : Reach 105671 := (sr 1 105671 158507 (by norm_num) (by norm_num) (sr 1 158507 237761 (by norm_num) (by norm_num) (sr 2 237761 178321 (by norm_num) (by norm_num) (sr 2 178321 133741 (by norm_num) (by norm_num) (sr 3 133741 50153 (by norm_num) (by norm_num) (B 50153 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R105675 : Reach 105675 := (sr 1 105675 158513 (by norm_num) (by norm_num) (sr 2 158513 118885 (by norm_num) (by norm_num) (sr 4 118885 22291 (by norm_num) (by norm_num) (B 22291 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105679 : Reach 105679 := (sr 1 105679 158519 (by norm_num) (by norm_num) (sr 1 158519 237779 (by norm_num) (by norm_num) (sr 1 237779 356669 (by norm_num) (by norm_num) (sr 3 356669 133751 (by norm_num) (by norm_num) (sr 1 133751 200627 (by norm_num) (by norm_num) (sr 1 200627 300941 (by norm_num) (by norm_num) (sr 3 300941 112853 (by norm_num) (by norm_num) (sr 7 112853 2645 (by norm_num) (by norm_num) (B 2645 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R105683 : Reach 105683 := (sr 1 105683 158525 (by norm_num) (by norm_num) (sr 3 158525 59447 (by norm_num) (by norm_num) (B 59447 (by norm_num) (by norm_num) (by norm_num))))
theorem R105687 : Reach 105687 := (sr 1 105687 158531 (by norm_num) (by norm_num) (sr 1 158531 237797 (by norm_num) (by norm_num) (sr 4 237797 44587 (by norm_num) (by norm_num) (B 44587 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105691 : Reach 105691 := (sr 1 105691 158537 (by norm_num) (by norm_num) (sr 2 158537 118903 (by norm_num) (by norm_num) (sr 1 118903 178355 (by norm_num) (by norm_num) (sr 1 178355 267533 (by norm_num) (by norm_num) (sr 3 267533 100325 (by norm_num) (by norm_num) (sr 4 100325 18811 (by norm_num) (by norm_num) (B 18811 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105695 : Reach 105695 := (sr 1 105695 158543 (by norm_num) (by norm_num) (sr 1 158543 237815 (by norm_num) (by norm_num) (sr 1 237815 356723 (by norm_num) (by norm_num) (sr 1 356723 535085 (by norm_num) (by norm_num) (sr 3 535085 200657 (by norm_num) (by norm_num) (sr 2 200657 150493 (by norm_num) (by norm_num) (sr 3 150493 56435 (by norm_num) (by norm_num) (B 56435 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R105699 : Reach 105699 := (sr 1 105699 158549 (by norm_num) (by norm_num) (sr 9 158549 929 (by norm_num) (by norm_num) (B 929 (by norm_num) (by norm_num) (by norm_num))))
theorem R105703 : Reach 105703 := (sr 1 105703 158555 (by norm_num) (by norm_num) (sr 1 158555 237833 (by norm_num) (by norm_num) (sr 2 237833 178375 (by norm_num) (by norm_num) (sr 1 178375 267563 (by norm_num) (by norm_num) (sr 1 267563 401345 (by norm_num) (by norm_num) (sr 2 401345 301009 (by norm_num) (by norm_num) (sr 2 301009 225757 (by norm_num) (by norm_num) (sr 3 225757 84659 (by norm_num) (by norm_num) (B 84659 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R105707 : Reach 105707 := (sr 1 105707 158561 (by norm_num) (by norm_num) (sr 2 158561 118921 (by norm_num) (by norm_num) (sr 2 118921 89191 (by norm_num) (by norm_num) (B 89191 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105711 : Reach 105711 := (sr 1 105711 158567 (by norm_num) (by norm_num) (sr 1 158567 237851 (by norm_num) (by norm_num) (sr 1 237851 356777 (by norm_num) (by norm_num) (sr 2 356777 267583 (by norm_num) (by norm_num) (sr 1 267583 401375 (by norm_num) (by norm_num) (sr 1 401375 602063 (by norm_num) (by norm_num) (sr 1 602063 903095 (by norm_num) (by norm_num) (sr 1 903095 1354643 (by norm_num) (by norm_num) (sr 1 1354643 2031965 (by norm_num) (by norm_num) (sr 3 2031965 761987 (by norm_num) (by norm_num) (sr 1 761987 1142981 (by norm_num) (by norm_num) (sr 4 1142981 214309 (by norm_num) (by norm_num) (sr 4 214309 40183 (by norm_num) (by norm_num) (B 40183 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R105715 : Reach 105715 := (sr 1 105715 158573 (by norm_num) (by norm_num) (sr 3 158573 59465 (by norm_num) (by norm_num) (B 59465 (by norm_num) (by norm_num) (by norm_num))))
theorem R105719 : Reach 105719 := (sr 1 105719 158579 (by norm_num) (by norm_num) (sr 1 158579 237869 (by norm_num) (by norm_num) (sr 3 237869 89201 (by norm_num) (by norm_num) (B 89201 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105723 : Reach 105723 := (sr 1 105723 158585 (by norm_num) (by norm_num) (sr 2 158585 118939 (by norm_num) (by norm_num) (sr 1 118939 178409 (by norm_num) (by norm_num) (sr 2 178409 133807 (by norm_num) (by norm_num) (sr 1 133807 200711 (by norm_num) (by norm_num) (sr 1 200711 301067 (by norm_num) (by norm_num) (sr 1 301067 451601 (by norm_num) (by norm_num) (sr 2 451601 338701 (by norm_num) (by norm_num) (sr 3 338701 127013 (by norm_num) (by norm_num) (sr 4 127013 23815 (by norm_num) (by norm_num) (B 23815 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R105727 : Reach 105727 := (sr 1 105727 158591 (by norm_num) (by norm_num) (sr 1 158591 237887 (by norm_num) (by norm_num) (sr 1 237887 356831 (by norm_num) (by norm_num) (sr 1 356831 535247 (by norm_num) (by norm_num) (sr 1 535247 802871 (by norm_num) (by norm_num) (sr 1 802871 1204307 (by norm_num) (by norm_num) (sr 1 1204307 1806461 (by norm_num) (by norm_num) (sr 3 1806461 677423 (by norm_num) (by norm_num) (sr 1 677423 1016135 (by norm_num) (by norm_num) (sr 1 1016135 1524203 (by norm_num) (by norm_num) (sr 1 1524203 2286305 (by norm_num) (by norm_num) (sr 2 2286305 1714729 (by norm_num) (by norm_num) (sr 2 1714729 1286047 (by norm_num) (by norm_num) (sr 1 1286047 1929071 (by norm_num) (by norm_num) (sr 1 1929071 2893607 (by norm_num) (by norm_num) (sr 1 2893607 4340411 (by norm_num) (by norm_num) (sr 1 4340411 6510617 (by norm_num) (by norm_num) (sr 2 6510617 4882963 (by norm_num) (by norm_num) (sr 1 4882963 7324445 (by norm_num) (by norm_num) (sr 3 7324445 2746667 (by norm_num) (by norm_num) (sr 1 2746667 4120001 (by norm_num) (by norm_num) (sr 2 4120001 3090001 (by norm_num) (by norm_num) (sr 2 3090001 2317501 (by norm_num) (by norm_num) (sr 3 2317501 869063 (by norm_num) (by norm_num) (sr 1 869063 1303595 (by norm_num) (by norm_num) (sr 1 1303595 1955393 (by norm_num) (by norm_num) (sr 2 1955393 1466545 (by norm_num) (by norm_num) (sr 2 1466545 1099909 (by norm_num) (by norm_num) (sr 4 1099909 206233 (by norm_num) (by norm_num) (sr 2 206233 154675 (by norm_num) (by norm_num) (sr 1 154675 232013 (by norm_num) (by norm_num) (sr 3 232013 87005 (by norm_num) (by norm_num) (B 87005 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))))))
theorem R105731 : Reach 105731 := (sr 1 105731 158597 (by norm_num) (by norm_num) (sr 4 158597 29737 (by norm_num) (by norm_num) (B 29737 (by norm_num) (by norm_num) (by norm_num))))
theorem R105735 : Reach 105735 := (sr 1 105735 158603 (by norm_num) (by norm_num) (sr 1 158603 237905 (by norm_num) (by norm_num) (sr 2 237905 178429 (by norm_num) (by norm_num) (sr 3 178429 66911 (by norm_num) (by norm_num) (B 66911 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105739 : Reach 105739 := (sr 1 105739 158609 (by norm_num) (by norm_num) (sr 2 158609 118957 (by norm_num) (by norm_num) (sr 3 118957 44609 (by norm_num) (by norm_num) (B 44609 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105743 : Reach 105743 := (sr 1 105743 158615 (by norm_num) (by norm_num) (sr 1 158615 237923 (by norm_num) (by norm_num) (sr 1 237923 356885 (by norm_num) (by norm_num) (sr 6 356885 16729 (by norm_num) (by norm_num) (B 16729 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105747 : Reach 105747 := (sr 1 105747 158621 (by norm_num) (by norm_num) (sr 3 158621 59483 (by norm_num) (by norm_num) (B 59483 (by norm_num) (by norm_num) (by norm_num))))
theorem R105751 : Reach 105751 := (sr 1 105751 158627 (by norm_num) (by norm_num) (sr 1 158627 237941 (by norm_num) (by norm_num) (sr 5 237941 22307 (by norm_num) (by norm_num) (B 22307 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105755 : Reach 105755 := (sr 1 105755 158633 (by norm_num) (by norm_num) (sr 2 158633 118975 (by norm_num) (by norm_num) (sr 1 118975 178463 (by norm_num) (by norm_num) (sr 1 178463 267695 (by norm_num) (by norm_num) (sr 1 267695 401543 (by norm_num) (by norm_num) (sr 1 401543 602315 (by norm_num) (by norm_num) (sr 1 602315 903473 (by norm_num) (by norm_num) (sr 2 903473 677605 (by norm_num) (by norm_num) (sr 4 677605 127051 (by norm_num) (by norm_num) (sr 1 127051 190577 (by norm_num) (by norm_num) (sr 2 190577 142933 (by norm_num) (by norm_num) (sr 8 142933 1675 (by norm_num) (by norm_num) (B 1675 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R105759 : Reach 105759 := (sr 1 105759 158639 (by norm_num) (by norm_num) (sr 1 158639 237959 (by norm_num) (by norm_num) (sr 1 237959 356939 (by norm_num) (by norm_num) (sr 1 356939 535409 (by norm_num) (by norm_num) (sr 2 535409 401557 (by norm_num) (by norm_num) (sr 6 401557 18823 (by norm_num) (by norm_num) (B 18823 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105763 : Reach 105763 := (sr 1 105763 158645 (by norm_num) (by norm_num) (sr 5 158645 14873 (by norm_num) (by norm_num) (B 14873 (by norm_num) (by norm_num) (by norm_num))))
theorem R105767 : Reach 105767 := (sr 1 105767 158651 (by norm_num) (by norm_num) (sr 1 158651 237977 (by norm_num) (by norm_num) (sr 2 237977 178483 (by norm_num) (by norm_num) (sr 1 178483 267725 (by norm_num) (by norm_num) (sr 3 267725 100397 (by norm_num) (by norm_num) (sr 3 100397 37649 (by norm_num) (by norm_num) (B 37649 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105771 : Reach 105771 := (sr 1 105771 158657 (by norm_num) (by norm_num) (sr 2 158657 118993 (by norm_num) (by norm_num) (sr 2 118993 89245 (by norm_num) (by norm_num) (B 89245 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105775 : Reach 105775 := (sr 1 105775 158663 (by norm_num) (by norm_num) (sr 1 158663 237995 (by norm_num) (by norm_num) (sr 1 237995 356993 (by norm_num) (by norm_num) (sr 2 356993 267745 (by norm_num) (by norm_num) (sr 2 267745 200809 (by norm_num) (by norm_num) (sr 2 200809 150607 (by norm_num) (by norm_num) (sr 1 150607 225911 (by norm_num) (by norm_num) (sr 1 225911 338867 (by norm_num) (by norm_num) (sr 1 338867 508301 (by norm_num) (by norm_num) (sr 3 508301 190613 (by norm_num) (by norm_num) (sr 6 190613 8935 (by norm_num) (by norm_num) (B 8935 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R105779 : Reach 105779 := (sr 1 105779 158669 (by norm_num) (by norm_num) (sr 3 158669 59501 (by norm_num) (by norm_num) (B 59501 (by norm_num) (by norm_num) (by norm_num))))
theorem R105783 : Reach 105783 := (sr 1 105783 158675 (by norm_num) (by norm_num) (sr 1 158675 238013 (by norm_num) (by norm_num) (sr 3 238013 89255 (by norm_num) (by norm_num) (B 89255 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105787 : Reach 105787 := (sr 1 105787 158681 (by norm_num) (by norm_num) (sr 2 158681 119011 (by norm_num) (by norm_num) (sr 1 119011 178517 (by norm_num) (by norm_num) (sr 10 178517 523 (by norm_num) (by norm_num) (B 523 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105791 : Reach 105791 := (sr 1 105791 158687 (by norm_num) (by norm_num) (sr 1 158687 238031 (by norm_num) (by norm_num) (sr 1 238031 357047 (by norm_num) (by norm_num) (sr 1 357047 535571 (by norm_num) (by norm_num) (sr 1 535571 803357 (by norm_num) (by norm_num) (sr 3 803357 301259 (by norm_num) (by norm_num) (sr 1 301259 451889 (by norm_num) (by norm_num) (sr 2 451889 338917 (by norm_num) (by norm_num) (sr 4 338917 63547 (by norm_num) (by norm_num) (B 63547 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R105795 : Reach 105795 := (sr 1 105795 158693 (by norm_num) (by norm_num) (sr 4 158693 29755 (by norm_num) (by norm_num) (B 29755 (by norm_num) (by norm_num) (by norm_num))))
theorem R105799 : Reach 105799 := (sr 1 105799 158699 (by norm_num) (by norm_num) (sr 1 158699 238049 (by norm_num) (by norm_num) (sr 2 238049 178537 (by norm_num) (by norm_num) (sr 2 178537 133903 (by norm_num) (by norm_num) (sr 1 133903 200855 (by norm_num) (by norm_num) (sr 1 200855 301283 (by norm_num) (by norm_num) (sr 1 301283 451925 (by norm_num) (by norm_num) (sr 12 451925 331 (by norm_num) (by norm_num) (B 331 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R105803 : Reach 105803 := (sr 1 105803 158705 (by norm_num) (by norm_num) (sr 2 158705 119029 (by norm_num) (by norm_num) (sr 5 119029 11159 (by norm_num) (by norm_num) (B 11159 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105807 : Reach 105807 := (sr 1 105807 158711 (by norm_num) (by norm_num) (sr 1 158711 238067 (by norm_num) (by norm_num) (sr 1 238067 357101 (by norm_num) (by norm_num) (sr 3 357101 133913 (by norm_num) (by norm_num) (sr 2 133913 100435 (by norm_num) (by norm_num) R100435)))))
theorem R105811 : Reach 105811 := (sr 1 105811 158717 (by norm_num) (by norm_num) (sr 3 158717 59519 (by norm_num) (by norm_num) (B 59519 (by norm_num) (by norm_num) (by norm_num))))
theorem R105815 : Reach 105815 := (sr 1 105815 158723 (by norm_num) (by norm_num) (sr 1 158723 238085 (by norm_num) (by norm_num) (sr 4 238085 44641 (by norm_num) (by norm_num) (B 44641 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105819 : Reach 105819 := (sr 1 105819 158729 (by norm_num) (by norm_num) (sr 2 158729 119047 (by norm_num) (by norm_num) (sr 1 119047 178571 (by norm_num) (by norm_num) (sr 1 178571 267857 (by norm_num) (by norm_num) (sr 2 267857 200893 (by norm_num) (by norm_num) (sr 3 200893 75335 (by norm_num) (by norm_num) (B 75335 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105823 : Reach 105823 := (sr 1 105823 158735 (by norm_num) (by norm_num) (sr 1 158735 238103 (by norm_num) (by norm_num) (sr 1 238103 357155 (by norm_num) (by norm_num) (sr 1 357155 535733 (by norm_num) (by norm_num) (sr 5 535733 50225 (by norm_num) (by norm_num) (B 50225 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R105827 : Reach 105827 := (sr 1 105827 158741 (by norm_num) (by norm_num) (sr 6 158741 7441 (by norm_num) (by norm_num) (B 7441 (by norm_num) (by norm_num) (by norm_num))))
theorem R105831 : Reach 105831 := (sr 1 105831 158747 (by norm_num) (by norm_num) (sr 1 158747 238121 (by norm_num) (by norm_num) (sr 2 238121 178591 (by norm_num) (by norm_num) (sr 1 178591 267887 (by norm_num) (by norm_num) (sr 1 267887 401831 (by norm_num) (by norm_num) (sr 1 401831 602747 (by norm_num) (by norm_num) (sr 1 602747 904121 (by norm_num) (by norm_num) (sr 2 904121 678091 (by norm_num) (by norm_num) (sr 1 678091 1017137 (by norm_num) (by norm_num) (sr 2 1017137 762853 (by norm_num) (by norm_num) (sr 4 762853 143035 (by norm_num) (by norm_num) (sr 1 143035 214553 (by norm_num) (by norm_num) (sr 2 214553 160915 (by norm_num) (by norm_num) (sr 1 160915 241373 (by norm_num) (by norm_num) (sr 3 241373 90515 (by norm_num) (by norm_num) (B 90515 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R105835 : Reach 105835 := (sr 1 105835 158753 (by norm_num) (by norm_num) (sr 2 158753 119065 (by norm_num) (by norm_num) (sr 2 119065 89299 (by norm_num) (by norm_num) (B 89299 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105839 : Reach 105839 := (sr 1 105839 158759 (by norm_num) (by norm_num) (sr 1 158759 238139 (by norm_num) (by norm_num) (sr 1 238139 357209 (by norm_num) (by norm_num) (sr 2 357209 267907 (by norm_num) (by norm_num) (sr 1 267907 401861 (by norm_num) (by norm_num) (sr 4 401861 75349 (by norm_num) (by norm_num) (B 75349 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105843 : Reach 105843 := (sr 1 105843 158765 (by norm_num) (by norm_num) (sr 3 158765 59537 (by norm_num) (by norm_num) (B 59537 (by norm_num) (by norm_num) (by norm_num))))
theorem R105847 : Reach 105847 := (sr 1 105847 158771 (by norm_num) (by norm_num) (sr 1 158771 238157 (by norm_num) (by norm_num) (sr 3 238157 89309 (by norm_num) (by norm_num) (B 89309 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105851 : Reach 105851 := (sr 1 105851 158777 (by norm_num) (by norm_num) (sr 2 158777 119083 (by norm_num) (by norm_num) (sr 1 119083 178625 (by norm_num) (by norm_num) (sr 2 178625 133969 (by norm_num) (by norm_num) (sr 2 133969 100477 (by norm_num) (by norm_num) (sr 3 100477 37679 (by norm_num) (by norm_num) (B 37679 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105855 : Reach 105855 := (sr 1 105855 158783 (by norm_num) (by norm_num) (sr 1 158783 238175 (by norm_num) (by norm_num) (sr 1 238175 357263 (by norm_num) (by norm_num) (sr 1 357263 535895 (by norm_num) (by norm_num) (sr 1 535895 803843 (by norm_num) (by norm_num) (sr 1 803843 1205765 (by norm_num) (by norm_num) (sr 4 1205765 226081 (by norm_num) (by norm_num) (sr 2 226081 169561 (by norm_num) (by norm_num) (sr 2 169561 127171 (by norm_num) (by norm_num) (sr 1 127171 190757 (by norm_num) (by norm_num) (sr 4 190757 35767 (by norm_num) (by norm_num) (B 35767 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R105859 : Reach 105859 := (sr 1 105859 158789 (by norm_num) (by norm_num) (sr 4 158789 29773 (by norm_num) (by norm_num) (B 29773 (by norm_num) (by norm_num) (by norm_num))))
theorem R105863 : Reach 105863 := (sr 1 105863 158795 (by norm_num) (by norm_num) (sr 1 158795 238193 (by norm_num) (by norm_num) (sr 2 238193 178645 (by norm_num) (by norm_num) (sr 7 178645 4187 (by norm_num) (by norm_num) (B 4187 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105867 : Reach 105867 := (sr 1 105867 158801 (by norm_num) (by norm_num) (sr 2 158801 119101 (by norm_num) (by norm_num) (sr 3 119101 44663 (by norm_num) (by norm_num) (B 44663 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105871 : Reach 105871 := (sr 1 105871 158807 (by norm_num) (by norm_num) (sr 1 158807 238211 (by norm_num) (by norm_num) (sr 1 238211 357317 (by norm_num) (by norm_num) (sr 4 357317 66997 (by norm_num) (by norm_num) (B 66997 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105875 : Reach 105875 := (sr 1 105875 158813 (by norm_num) (by norm_num) (sr 3 158813 59555 (by norm_num) (by norm_num) (B 59555 (by norm_num) (by norm_num) (by norm_num))))
theorem R105879 : Reach 105879 := (sr 1 105879 158819 (by norm_num) (by norm_num) (sr 1 158819 238229 (by norm_num) (by norm_num) (sr 6 238229 11167 (by norm_num) (by norm_num) (B 11167 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105883 : Reach 105883 := (sr 1 105883 158825 (by norm_num) (by norm_num) (sr 2 158825 119119 (by norm_num) (by norm_num) (sr 1 119119 178679 (by norm_num) (by norm_num) (sr 1 178679 268019 (by norm_num) (by norm_num) (sr 1 268019 402029 (by norm_num) (by norm_num) (sr 3 402029 150761 (by norm_num) (by norm_num) (sr 2 150761 113071 (by norm_num) (by norm_num) (sr 1 113071 169607 (by norm_num) (by norm_num) (sr 1 169607 254411 (by norm_num) (by norm_num) (sr 1 254411 381617 (by norm_num) (by norm_num) (sr 2 381617 286213 (by norm_num) (by norm_num) (sr 4 286213 53665 (by norm_num) (by norm_num) (B 53665 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R105887 : Reach 105887 := (sr 1 105887 158831 (by norm_num) (by norm_num) (sr 1 158831 238247 (by norm_num) (by norm_num) (sr 1 238247 357371 (by norm_num) (by norm_num) (sr 1 357371 536057 (by norm_num) (by norm_num) (sr 2 536057 402043 (by norm_num) (by norm_num) (sr 1 402043 603065 (by norm_num) (by norm_num) (sr 2 603065 452299 (by norm_num) (by norm_num) (sr 1 452299 678449 (by norm_num) (by norm_num) (sr 2 678449 508837 (by norm_num) (by norm_num) (sr 4 508837 95407 (by norm_num) (by norm_num) (B 95407 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R105891 : Reach 105891 := (sr 1 105891 158837 (by norm_num) (by norm_num) (sr 5 158837 14891 (by norm_num) (by norm_num) (B 14891 (by norm_num) (by norm_num) (by norm_num))))
theorem R105895 : Reach 105895 := (sr 1 105895 158843 (by norm_num) (by norm_num) (sr 1 158843 238265 (by norm_num) (by norm_num) (sr 2 238265 178699 (by norm_num) (by norm_num) (sr 1 178699 268049 (by norm_num) (by norm_num) (sr 2 268049 201037 (by norm_num) (by norm_num) (sr 3 201037 75389 (by norm_num) (by norm_num) (B 75389 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105899 : Reach 105899 := (sr 1 105899 158849 (by norm_num) (by norm_num) (sr 2 158849 119137 (by norm_num) (by norm_num) (sr 2 119137 89353 (by norm_num) (by norm_num) (B 89353 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105903 : Reach 105903 := (sr 1 105903 158855 (by norm_num) (by norm_num) (sr 1 158855 238283 (by norm_num) (by norm_num) (sr 1 238283 357425 (by norm_num) (by norm_num) (sr 2 357425 268069 (by norm_num) (by norm_num) (sr 4 268069 50263 (by norm_num) (by norm_num) (B 50263 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R105907 : Reach 105907 := (sr 1 105907 158861 (by norm_num) (by norm_num) (sr 3 158861 59573 (by norm_num) (by norm_num) (B 59573 (by norm_num) (by norm_num) (by norm_num))))
theorem R105911 : Reach 105911 := (sr 1 105911 158867 (by norm_num) (by norm_num) (sr 1 158867 238301 (by norm_num) (by norm_num) (sr 3 238301 89363 (by norm_num) (by norm_num) (B 89363 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105915 : Reach 105915 := (sr 1 105915 158873 (by norm_num) (by norm_num) (sr 2 158873 119155 (by norm_num) (by norm_num) (sr 1 119155 178733 (by norm_num) (by norm_num) (sr 3 178733 67025 (by norm_num) (by norm_num) (B 67025 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105919 : Reach 105919 := (sr 1 105919 158879 (by norm_num) (by norm_num) (sr 1 158879 238319 (by norm_num) (by norm_num) (sr 1 238319 357479 (by norm_num) (by norm_num) (sr 1 357479 536219 (by norm_num) (by norm_num) (sr 1 536219 804329 (by norm_num) (by norm_num) (sr 2 804329 603247 (by norm_num) (by norm_num) (sr 1 603247 904871 (by norm_num) (by norm_num) (sr 1 904871 1357307 (by norm_num) (by norm_num) (sr 1 1357307 2035961 (by norm_num) (by norm_num) (sr 2 2035961 1526971 (by norm_num) (by norm_num) (sr 1 1526971 2290457 (by norm_num) (by norm_num) (sr 2 2290457 1717843 (by norm_num) (by norm_num) (sr 1 1717843 2576765 (by norm_num) (by norm_num) (sr 3 2576765 966287 (by norm_num) (by norm_num) (sr 1 966287 1449431 (by norm_num) (by norm_num) (sr 1 1449431 2174147 (by norm_num) (by norm_num) (sr 1 2174147 3261221 (by norm_num) (by norm_num) (sr 4 3261221 611479 (by norm_num) (by norm_num) (sr 1 611479 917219 (by norm_num) (by norm_num) (sr 1 917219 1375829 (by norm_num) (by norm_num) (sr 8 1375829 16123 (by norm_num) (by norm_num) (B 16123 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))
theorem R105923 : Reach 105923 := (sr 1 105923 158885 (by norm_num) (by norm_num) (sr 4 158885 29791 (by norm_num) (by norm_num) (B 29791 (by norm_num) (by norm_num) (by norm_num))))
theorem R105927 : Reach 105927 := (sr 1 105927 158891 (by norm_num) (by norm_num) (sr 1 158891 238337 (by norm_num) (by norm_num) (sr 2 238337 178753 (by norm_num) (by norm_num) (sr 2 178753 134065 (by norm_num) (by norm_num) (sr 2 134065 100549 (by norm_num) (by norm_num) (sr 4 100549 18853 (by norm_num) (by norm_num) (B 18853 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105931 : Reach 105931 := (sr 1 105931 158897 (by norm_num) (by norm_num) (sr 2 158897 119173 (by norm_num) (by norm_num) (sr 4 119173 22345 (by norm_num) (by norm_num) (B 22345 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105935 : Reach 105935 := (sr 1 105935 158903 (by norm_num) (by norm_num) (sr 1 158903 238355 (by norm_num) (by norm_num) (sr 1 238355 357533 (by norm_num) (by norm_num) (sr 3 357533 134075 (by norm_num) (by norm_num) (sr 1 134075 201113 (by norm_num) (by norm_num) (sr 2 201113 150835 (by norm_num) (by norm_num) (sr 1 150835 226253 (by norm_num) (by norm_num) (sr 3 226253 84845 (by norm_num) (by norm_num) (B 84845 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R105939 : Reach 105939 := (sr 1 105939 158909 (by norm_num) (by norm_num) (sr 3 158909 59591 (by norm_num) (by norm_num) (B 59591 (by norm_num) (by norm_num) (by norm_num))))
theorem R105943 : Reach 105943 := (sr 1 105943 158915 (by norm_num) (by norm_num) (sr 1 158915 238373 (by norm_num) (by norm_num) (sr 4 238373 44695 (by norm_num) (by norm_num) (B 44695 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105947 : Reach 105947 := (sr 1 105947 158921 (by norm_num) (by norm_num) (sr 2 158921 119191 (by norm_num) (by norm_num) (sr 1 119191 178787 (by norm_num) (by norm_num) (sr 1 178787 268181 (by norm_num) (by norm_num) (sr 6 268181 12571 (by norm_num) (by norm_num) (B 12571 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R105951 : Reach 105951 := (sr 1 105951 158927 (by norm_num) (by norm_num) (sr 1 158927 238391 (by norm_num) (by norm_num) (sr 1 238391 357587 (by norm_num) (by norm_num) (sr 1 357587 536381 (by norm_num) (by norm_num) (sr 3 536381 201143 (by norm_num) (by norm_num) (sr 1 201143 301715 (by norm_num) (by norm_num) (sr 1 301715 452573 (by norm_num) (by norm_num) (sr 3 452573 169715 (by norm_num) (by norm_num) (sr 1 169715 254573 (by norm_num) (by norm_num) (sr 3 254573 95465 (by norm_num) (by norm_num) (B 95465 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R105955 : Reach 105955 := (sr 1 105955 158933 (by norm_num) (by norm_num) (sr 7 158933 3725 (by norm_num) (by norm_num) (B 3725 (by norm_num) (by norm_num) (by norm_num))))
theorem R105959 : Reach 105959 := (sr 1 105959 158939 (by norm_num) (by norm_num) (sr 1 158939 238409 (by norm_num) (by norm_num) (sr 2 238409 178807 (by norm_num) (by norm_num) (sr 1 178807 268211 (by norm_num) (by norm_num) (sr 1 268211 402317 (by norm_num) (by norm_num) (sr 3 402317 150869 (by norm_num) (by norm_num) (sr 11 150869 221 (by norm_num) (by norm_num) (B 221 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R105963 : Reach 105963 := (sr 1 105963 158945 (by norm_num) (by norm_num) (sr 2 158945 119209 (by norm_num) (by norm_num) (sr 2 119209 89407 (by norm_num) (by norm_num) (B 89407 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105967 : Reach 105967 := (sr 1 105967 158951 (by norm_num) (by norm_num) (sr 1 158951 238427 (by norm_num) (by norm_num) (sr 1 238427 357641 (by norm_num) (by norm_num) (sr 2 357641 268231 (by norm_num) (by norm_num) (sr 1 268231 402347 (by norm_num) (by norm_num) (sr 1 402347 603521 (by norm_num) (by norm_num) (sr 2 603521 452641 (by norm_num) (by norm_num) (sr 2 452641 339481 (by norm_num) (by norm_num) (sr 2 339481 254611 (by norm_num) (by norm_num) (sr 1 254611 381917 (by norm_num) (by norm_num) (sr 3 381917 143219 (by norm_num) (by norm_num) (sr 1 143219 214829 (by norm_num) (by norm_num) (sr 3 214829 80561 (by norm_num) (by norm_num) (B 80561 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R105971 : Reach 105971 := (sr 1 105971 158957 (by norm_num) (by norm_num) (sr 3 158957 59609 (by norm_num) (by norm_num) (B 59609 (by norm_num) (by norm_num) (by norm_num))))
theorem R105975 : Reach 105975 := (sr 1 105975 158963 (by norm_num) (by norm_num) (sr 1 158963 238445 (by norm_num) (by norm_num) (sr 3 238445 89417 (by norm_num) (by norm_num) (B 89417 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105979 : Reach 105979 := (sr 1 105979 158969 (by norm_num) (by norm_num) (sr 2 158969 119227 (by norm_num) (by norm_num) (sr 1 119227 178841 (by norm_num) (by norm_num) (sr 2 178841 134131 (by norm_num) (by norm_num) (sr 1 134131 201197 (by norm_num) (by norm_num) (sr 3 201197 75449 (by norm_num) (by norm_num) (B 75449 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R105983 : Reach 105983 := (sr 1 105983 158975 (by norm_num) (by norm_num) (sr 1 158975 238463 (by norm_num) (by norm_num) (sr 1 238463 357695 (by norm_num) (by norm_num) (sr 1 357695 536543 (by norm_num) (by norm_num) (sr 1 536543 804815 (by norm_num) (by norm_num) (sr 1 804815 1207223 (by norm_num) (by norm_num) (sr 1 1207223 1810835 (by norm_num) (by norm_num) (sr 1 1810835 2716253 (by norm_num) (by norm_num) (sr 3 2716253 1018595 (by norm_num) (by norm_num) (sr 1 1018595 1527893 (by norm_num) (by norm_num) (sr 8 1527893 17905 (by norm_num) (by norm_num) (B 17905 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R105987 : Reach 105987 := (sr 1 105987 158981 (by norm_num) (by norm_num) (sr 4 158981 29809 (by norm_num) (by norm_num) (B 29809 (by norm_num) (by norm_num) (by norm_num))))
theorem R105991 : Reach 105991 := (sr 1 105991 158987 (by norm_num) (by norm_num) (sr 1 158987 238481 (by norm_num) (by norm_num) (sr 2 238481 178861 (by norm_num) (by norm_num) (sr 3 178861 67073 (by norm_num) (by norm_num) (B 67073 (by norm_num) (by norm_num) (by norm_num))))))
theorem R105995 : Reach 105995 := (sr 1 105995 158993 (by norm_num) (by norm_num) (sr 2 158993 119245 (by norm_num) (by norm_num) (sr 3 119245 44717 (by norm_num) (by norm_num) (B 44717 (by norm_num) (by norm_num) (by norm_num)))))
theorem R105999 : Reach 105999 := (sr 1 105999 158999 (by norm_num) (by norm_num) (sr 1 158999 238499 (by norm_num) (by norm_num) (sr 1 238499 357749 (by norm_num) (by norm_num) (sr 5 357749 33539 (by norm_num) (by norm_num) (B 33539 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106003 : Reach 106003 := (sr 1 106003 159005 (by norm_num) (by norm_num) (sr 3 159005 59627 (by norm_num) (by norm_num) (B 59627 (by norm_num) (by norm_num) (by norm_num))))
theorem R106007 : Reach 106007 := (sr 1 106007 159011 (by norm_num) (by norm_num) (sr 1 159011 238517 (by norm_num) (by norm_num) (sr 5 238517 22361 (by norm_num) (by norm_num) (B 22361 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106011 : Reach 106011 := (sr 1 106011 159017 (by norm_num) (by norm_num) (sr 2 159017 119263 (by norm_num) (by norm_num) (sr 1 119263 178895 (by norm_num) (by norm_num) (sr 1 178895 268343 (by norm_num) (by norm_num) (sr 1 268343 402515 (by norm_num) (by norm_num) (sr 1 402515 603773 (by norm_num) (by norm_num) (sr 3 603773 226415 (by norm_num) (by norm_num) (sr 1 226415 339623 (by norm_num) (by norm_num) (sr 1 339623 509435 (by norm_num) (by norm_num) (sr 1 509435 764153 (by norm_num) (by norm_num) (sr 2 764153 573115 (by norm_num) (by norm_num) (sr 1 573115 859673 (by norm_num) (by norm_num) (sr 2 859673 644755 (by norm_num) (by norm_num) (sr 1 644755 967133 (by norm_num) (by norm_num) (sr 3 967133 362675 (by norm_num) (by norm_num) (sr 1 362675 544013 (by norm_num) (by norm_num) (sr 3 544013 204005 (by norm_num) (by norm_num) (sr 4 204005 38251 (by norm_num) (by norm_num) (B 38251 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))
theorem R106015 : Reach 106015 := (sr 1 106015 159023 (by norm_num) (by norm_num) (sr 1 159023 238535 (by norm_num) (by norm_num) (sr 1 238535 357803 (by norm_num) (by norm_num) (sr 1 357803 536705 (by norm_num) (by norm_num) (sr 2 536705 402529 (by norm_num) (by norm_num) (sr 2 402529 301897 (by norm_num) (by norm_num) (sr 2 301897 226423 (by norm_num) (by norm_num) (sr 1 226423 339635 (by norm_num) (by norm_num) (sr 1 339635 509453 (by norm_num) (by norm_num) (sr 3 509453 191045 (by norm_num) (by norm_num) (sr 4 191045 35821 (by norm_num) (by norm_num) (B 35821 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R106019 : Reach 106019 := (sr 1 106019 159029 (by norm_num) (by norm_num) (sr 5 159029 14909 (by norm_num) (by norm_num) (B 14909 (by norm_num) (by norm_num) (by norm_num))))
theorem R106023 : Reach 106023 := (sr 1 106023 159035 (by norm_num) (by norm_num) (sr 1 159035 238553 (by norm_num) (by norm_num) (sr 2 238553 178915 (by norm_num) (by norm_num) (sr 1 178915 268373 (by norm_num) (by norm_num) (sr 8 268373 3145 (by norm_num) (by norm_num) (B 3145 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R106027 : Reach 106027 := (sr 1 106027 159041 (by norm_num) (by norm_num) (sr 2 159041 119281 (by norm_num) (by norm_num) (sr 2 119281 89461 (by norm_num) (by norm_num) (B 89461 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106031 : Reach 106031 := (sr 1 106031 159047 (by norm_num) (by norm_num) (sr 1 159047 238571 (by norm_num) (by norm_num) (sr 1 238571 357857 (by norm_num) (by norm_num) (sr 2 357857 268393 (by norm_num) (by norm_num) (sr 2 268393 201295 (by norm_num) (by norm_num) (sr 1 201295 301943 (by norm_num) (by norm_num) (sr 1 301943 452915 (by norm_num) (by norm_num) (sr 1 452915 679373 (by norm_num) (by norm_num) (sr 3 679373 254765 (by norm_num) (by norm_num) (sr 3 254765 95537 (by norm_num) (by norm_num) (B 95537 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R106035 : Reach 106035 := (sr 1 106035 159053 (by norm_num) (by norm_num) (sr 3 159053 59645 (by norm_num) (by norm_num) (B 59645 (by norm_num) (by norm_num) (by norm_num))))
theorem R106039 : Reach 106039 := (sr 1 106039 159059 (by norm_num) (by norm_num) (sr 1 159059 238589 (by norm_num) (by norm_num) (sr 3 238589 89471 (by norm_num) (by norm_num) (B 89471 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106043 : Reach 106043 := (sr 1 106043 159065 (by norm_num) (by norm_num) (sr 2 159065 119299 (by norm_num) (by norm_num) (sr 1 119299 178949 (by norm_num) (by norm_num) (sr 4 178949 33553 (by norm_num) (by norm_num) (B 33553 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106047 : Reach 106047 := (sr 1 106047 159071 (by norm_num) (by norm_num) (sr 1 159071 238607 (by norm_num) (by norm_num) (sr 1 238607 357911 (by norm_num) (by norm_num) (sr 1 357911 536867 (by norm_num) (by norm_num) (sr 1 536867 805301 (by norm_num) (by norm_num) (sr 5 805301 75497 (by norm_num) (by norm_num) (B 75497 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106051 : Reach 106051 := (sr 1 106051 159077 (by norm_num) (by norm_num) (sr 4 159077 29827 (by norm_num) (by norm_num) (B 29827 (by norm_num) (by norm_num) (by norm_num))))
theorem R106055 : Reach 106055 := (sr 1 106055 159083 (by norm_num) (by norm_num) (sr 1 159083 238625 (by norm_num) (by norm_num) (sr 2 238625 178969 (by norm_num) (by norm_num) (sr 2 178969 134227 (by norm_num) (by norm_num) (sr 1 134227 201341 (by norm_num) (by norm_num) (sr 3 201341 75503 (by norm_num) (by norm_num) (B 75503 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106059 : Reach 106059 := (sr 1 106059 159089 (by norm_num) (by norm_num) (sr 2 159089 119317 (by norm_num) (by norm_num) (sr 6 119317 5593 (by norm_num) (by norm_num) (B 5593 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106063 : Reach 106063 := (sr 1 106063 159095 (by norm_num) (by norm_num) (sr 1 159095 238643 (by norm_num) (by norm_num) (sr 1 238643 357965 (by norm_num) (by norm_num) (sr 3 357965 134237 (by norm_num) (by norm_num) (sr 3 134237 50339 (by norm_num) (by norm_num) (B 50339 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R106067 : Reach 106067 := (sr 1 106067 159101 (by norm_num) (by norm_num) (sr 3 159101 59663 (by norm_num) (by norm_num) (B 59663 (by norm_num) (by norm_num) (by norm_num))))
theorem R106071 : Reach 106071 := (sr 1 106071 159107 (by norm_num) (by norm_num) (sr 1 159107 238661 (by norm_num) (by norm_num) (sr 4 238661 44749 (by norm_num) (by norm_num) (B 44749 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106075 : Reach 106075 := (sr 1 106075 159113 (by norm_num) (by norm_num) (sr 2 159113 119335 (by norm_num) (by norm_num) (sr 1 119335 179003 (by norm_num) (by norm_num) (sr 1 179003 268505 (by norm_num) (by norm_num) (sr 2 268505 201379 (by norm_num) (by norm_num) (sr 1 201379 302069 (by norm_num) (by norm_num) (sr 5 302069 28319 (by norm_num) (by norm_num) (B 28319 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R106079 : Reach 106079 := (sr 1 106079 159119 (by norm_num) (by norm_num) (sr 1 159119 238679 (by norm_num) (by norm_num) (sr 1 238679 358019 (by norm_num) (by norm_num) (sr 1 358019 537029 (by norm_num) (by norm_num) (sr 4 537029 100693 (by norm_num) (by norm_num) (sr 10 100693 295 (by norm_num) (by norm_num) (B 295 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106083 : Reach 106083 := (sr 1 106083 159125 (by norm_num) (by norm_num) (sr 6 159125 7459 (by norm_num) (by norm_num) (B 7459 (by norm_num) (by norm_num) (by norm_num))))
theorem R106087 : Reach 106087 := (sr 1 106087 159131 (by norm_num) (by norm_num) (sr 1 159131 238697 (by norm_num) (by norm_num) (sr 2 238697 179023 (by norm_num) (by norm_num) (sr 1 179023 268535 (by norm_num) (by norm_num) (sr 1 268535 402803 (by norm_num) (by norm_num) (sr 1 402803 604205 (by norm_num) (by norm_num) (sr 3 604205 226577 (by norm_num) (by norm_num) (sr 2 226577 169933 (by norm_num) (by norm_num) (sr 3 169933 63725 (by norm_num) (by norm_num) (B 63725 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R106091 : Reach 106091 := (sr 1 106091 159137 (by norm_num) (by norm_num) (sr 2 159137 119353 (by norm_num) (by norm_num) (sr 2 119353 89515 (by norm_num) (by norm_num) (B 89515 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106095 : Reach 106095 := (sr 1 106095 159143 (by norm_num) (by norm_num) (sr 1 159143 238715 (by norm_num) (by norm_num) (sr 1 238715 358073 (by norm_num) (by norm_num) (sr 2 358073 268555 (by norm_num) (by norm_num) (sr 1 268555 402833 (by norm_num) (by norm_num) (sr 2 402833 302125 (by norm_num) (by norm_num) (sr 3 302125 113297 (by norm_num) (by norm_num) (sr 2 113297 84973 (by norm_num) (by norm_num) (B 84973 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R106099 : Reach 106099 := (sr 1 106099 159149 (by norm_num) (by norm_num) (sr 3 159149 59681 (by norm_num) (by norm_num) (B 59681 (by norm_num) (by norm_num) (by norm_num))))
theorem R106103 : Reach 106103 := (sr 1 106103 159155 (by norm_num) (by norm_num) (sr 1 159155 238733 (by norm_num) (by norm_num) (sr 3 238733 89525 (by norm_num) (by norm_num) (B 89525 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106107 : Reach 106107 := (sr 1 106107 159161 (by norm_num) (by norm_num) (sr 2 159161 119371 (by norm_num) (by norm_num) (sr 1 119371 179057 (by norm_num) (by norm_num) (sr 2 179057 134293 (by norm_num) (by norm_num) (sr 6 134293 6295 (by norm_num) (by norm_num) (B 6295 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R106111 : Reach 106111 := (sr 1 106111 159167 (by norm_num) (by norm_num) (sr 1 159167 238751 (by norm_num) (by norm_num) (sr 1 238751 358127 (by norm_num) (by norm_num) (sr 1 358127 537191 (by norm_num) (by norm_num) (sr 1 537191 805787 (by norm_num) (by norm_num) (sr 1 805787 1208681 (by norm_num) (by norm_num) (sr 2 1208681 906511 (by norm_num) (by norm_num) (sr 1 906511 1359767 (by norm_num) (by norm_num) (sr 1 1359767 2039651 (by norm_num) (by norm_num) (sr 1 2039651 3059477 (by norm_num) (by norm_num) (sr 6 3059477 143413 (by norm_num) (by norm_num) (sr 5 143413 13445 (by norm_num) (by norm_num) (B 13445 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R106115 : Reach 106115 := (sr 1 106115 159173 (by norm_num) (by norm_num) (sr 4 159173 29845 (by norm_num) (by norm_num) (B 29845 (by norm_num) (by norm_num) (by norm_num))))
theorem R106119 : Reach 106119 := (sr 1 106119 159179 (by norm_num) (by norm_num) (sr 1 159179 238769 (by norm_num) (by norm_num) (sr 2 238769 179077 (by norm_num) (by norm_num) (sr 4 179077 33577 (by norm_num) (by norm_num) (B 33577 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106123 : Reach 106123 := (sr 1 106123 159185 (by norm_num) (by norm_num) (sr 2 159185 119389 (by norm_num) (by norm_num) (sr 3 119389 44771 (by norm_num) (by norm_num) (B 44771 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106127 : Reach 106127 := (sr 1 106127 159191 (by norm_num) (by norm_num) (sr 1 159191 238787 (by norm_num) (by norm_num) (sr 1 238787 358181 (by norm_num) (by norm_num) (sr 4 358181 67159 (by norm_num) (by norm_num) (B 67159 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106131 : Reach 106131 := (sr 1 106131 159197 (by norm_num) (by norm_num) (sr 3 159197 59699 (by norm_num) (by norm_num) (B 59699 (by norm_num) (by norm_num) (by norm_num))))
theorem R106135 : Reach 106135 := (sr 1 106135 159203 (by norm_num) (by norm_num) (sr 1 159203 238805 (by norm_num) (by norm_num) (sr 7 238805 5597 (by norm_num) (by norm_num) (B 5597 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106139 : Reach 106139 := (sr 1 106139 159209 (by norm_num) (by norm_num) (sr 2 159209 119407 (by norm_num) (by norm_num) (sr 1 119407 179111 (by norm_num) (by norm_num) (sr 1 179111 268667 (by norm_num) (by norm_num) (sr 1 268667 403001 (by norm_num) (by norm_num) (sr 2 403001 302251 (by norm_num) (by norm_num) (sr 1 302251 453377 (by norm_num) (by norm_num) (sr 2 453377 340033 (by norm_num) (by norm_num) (sr 2 340033 255025 (by norm_num) (by norm_num) (sr 2 255025 191269 (by norm_num) (by norm_num) (sr 4 191269 35863 (by norm_num) (by norm_num) (B 35863 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R106143 : Reach 106143 := (sr 1 106143 159215 (by norm_num) (by norm_num) (sr 1 159215 238823 (by norm_num) (by norm_num) (sr 1 238823 358235 (by norm_num) (by norm_num) (sr 1 358235 537353 (by norm_num) (by norm_num) (sr 2 537353 403015 (by norm_num) (by norm_num) (sr 1 403015 604523 (by norm_num) (by norm_num) (sr 1 604523 906785 (by norm_num) (by norm_num) (sr 2 906785 680089 (by norm_num) (by norm_num) (sr 2 680089 510067 (by norm_num) (by norm_num) (sr 1 510067 765101 (by norm_num) (by norm_num) (sr 3 765101 286913 (by norm_num) (by norm_num) (sr 2 286913 215185 (by norm_num) (by norm_num) (sr 2 215185 161389 (by norm_num) (by norm_num) (sr 3 161389 60521 (by norm_num) (by norm_num) (B 60521 (by norm_num) (by norm_num) (by norm_num))))))))))))))))
theorem R106147 : Reach 106147 := (sr 1 106147 159221 (by norm_num) (by norm_num) (sr 5 159221 14927 (by norm_num) (by norm_num) (B 14927 (by norm_num) (by norm_num) (by norm_num))))
theorem R106151 : Reach 106151 := (sr 1 106151 159227 (by norm_num) (by norm_num) (sr 1 159227 238841 (by norm_num) (by norm_num) (sr 2 238841 179131 (by norm_num) (by norm_num) (sr 1 179131 268697 (by norm_num) (by norm_num) (sr 2 268697 201523 (by norm_num) (by norm_num) (sr 1 201523 302285 (by norm_num) (by norm_num) (sr 3 302285 113357 (by norm_num) (by norm_num) (sr 3 113357 42509 (by norm_num) (by norm_num) (B 42509 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R106155 : Reach 106155 := (sr 1 106155 159233 (by norm_num) (by norm_num) (sr 2 159233 119425 (by norm_num) (by norm_num) (sr 2 119425 89569 (by norm_num) (by norm_num) (B 89569 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106159 : Reach 106159 := (sr 1 106159 159239 (by norm_num) (by norm_num) (sr 1 159239 238859 (by norm_num) (by norm_num) (sr 1 238859 358289 (by norm_num) (by norm_num) (sr 2 358289 268717 (by norm_num) (by norm_num) (sr 3 268717 100769 (by norm_num) (by norm_num) (sr 2 100769 75577 (by norm_num) (by norm_num) (B 75577 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106163 : Reach 106163 := (sr 1 106163 159245 (by norm_num) (by norm_num) (sr 3 159245 59717 (by norm_num) (by norm_num) (B 59717 (by norm_num) (by norm_num) (by norm_num))))
theorem R106167 : Reach 106167 := (sr 1 106167 159251 (by norm_num) (by norm_num) (sr 1 159251 238877 (by norm_num) (by norm_num) (sr 3 238877 89579 (by norm_num) (by norm_num) (B 89579 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106171 : Reach 106171 := (sr 1 106171 159257 (by norm_num) (by norm_num) (sr 2 159257 119443 (by norm_num) (by norm_num) (sr 1 119443 179165 (by norm_num) (by norm_num) (sr 3 179165 67187 (by norm_num) (by norm_num) (B 67187 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106175 : Reach 106175 := (sr 1 106175 159263 (by norm_num) (by norm_num) (sr 1 159263 238895 (by norm_num) (by norm_num) (sr 1 238895 358343 (by norm_num) (by norm_num) (sr 1 358343 537515 (by norm_num) (by norm_num) (sr 1 537515 806273 (by norm_num) (by norm_num) (sr 2 806273 604705 (by norm_num) (by norm_num) (sr 2 604705 453529 (by norm_num) (by norm_num) (sr 2 453529 340147 (by norm_num) (by norm_num) (sr 1 340147 510221 (by norm_num) (by norm_num) (sr 3 510221 191333 (by norm_num) (by norm_num) (sr 4 191333 35875 (by norm_num) (by norm_num) (B 35875 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R106179 : Reach 106179 := (sr 1 106179 159269 (by norm_num) (by norm_num) (sr 4 159269 29863 (by norm_num) (by norm_num) (B 29863 (by norm_num) (by norm_num) (by norm_num))))
theorem R106183 : Reach 106183 := (sr 1 106183 159275 (by norm_num) (by norm_num) (sr 1 159275 238913 (by norm_num) (by norm_num) (sr 2 238913 179185 (by norm_num) (by norm_num) (sr 2 179185 134389 (by norm_num) (by norm_num) (sr 5 134389 12599 (by norm_num) (by norm_num) (B 12599 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R106187 : Reach 106187 := (sr 1 106187 159281 (by norm_num) (by norm_num) (sr 2 159281 119461 (by norm_num) (by norm_num) (sr 4 119461 22399 (by norm_num) (by norm_num) (B 22399 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106191 : Reach 106191 := (sr 1 106191 159287 (by norm_num) (by norm_num) (sr 1 159287 238931 (by norm_num) (by norm_num) (sr 1 238931 358397 (by norm_num) (by norm_num) (sr 3 358397 134399 (by norm_num) (by norm_num) (sr 1 134399 201599 (by norm_num) (by norm_num) (sr 1 201599 302399 (by norm_num) (by norm_num) (sr 1 302399 453599 (by norm_num) (by norm_num) (sr 1 453599 680399 (by norm_num) (by norm_num) (sr 1 680399 1020599 (by norm_num) (by norm_num) (sr 1 1020599 1530899 (by norm_num) (by norm_num) (sr 1 1530899 2296349 (by norm_num) (by norm_num) (sr 3 2296349 861131 (by norm_num) (by norm_num) (sr 1 861131 1291697 (by norm_num) (by norm_num) (sr 2 1291697 968773 (by norm_num) (by norm_num) (sr 4 968773 181645 (by norm_num) (by norm_num) (sr 3 181645 68117 (by norm_num) (by norm_num) (B 68117 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))
theorem R106195 : Reach 106195 := (sr 1 106195 159293 (by norm_num) (by norm_num) (sr 3 159293 59735 (by norm_num) (by norm_num) (B 59735 (by norm_num) (by norm_num) (by norm_num))))
theorem R106199 : Reach 106199 := (sr 1 106199 159299 (by norm_num) (by norm_num) (sr 1 159299 238949 (by norm_num) (by norm_num) (sr 4 238949 44803 (by norm_num) (by norm_num) (B 44803 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106203 : Reach 106203 := (sr 1 106203 159305 (by norm_num) (by norm_num) (sr 2 159305 119479 (by norm_num) (by norm_num) (sr 1 119479 179219 (by norm_num) (by norm_num) (sr 1 179219 268829 (by norm_num) (by norm_num) (sr 3 268829 100811 (by norm_num) (by norm_num) R100811)))))
theorem R106207 : Reach 106207 := (sr 1 106207 159311 (by norm_num) (by norm_num) (sr 1 159311 238967 (by norm_num) (by norm_num) (sr 1 238967 358451 (by norm_num) (by norm_num) (sr 1 358451 537677 (by norm_num) (by norm_num) (sr 3 537677 201629 (by norm_num) (by norm_num) (sr 3 201629 75611 (by norm_num) (by norm_num) (B 75611 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106211 : Reach 106211 := (sr 1 106211 159317 (by norm_num) (by norm_num) (sr 8 159317 1867 (by norm_num) (by norm_num) (B 1867 (by norm_num) (by norm_num) (by norm_num))))
theorem R106215 : Reach 106215 := (sr 1 106215 159323 (by norm_num) (by norm_num) (sr 1 159323 238985 (by norm_num) (by norm_num) (sr 2 238985 179239 (by norm_num) (by norm_num) (sr 1 179239 268859 (by norm_num) (by norm_num) (sr 1 268859 403289 (by norm_num) (by norm_num) (sr 2 403289 302467 (by norm_num) (by norm_num) (sr 1 302467 453701 (by norm_num) (by norm_num) (sr 4 453701 85069 (by norm_num) (by norm_num) (B 85069 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R106219 : Reach 106219 := (sr 1 106219 159329 (by norm_num) (by norm_num) (sr 2 159329 119497 (by norm_num) (by norm_num) (sr 2 119497 89623 (by norm_num) (by norm_num) (B 89623 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106223 : Reach 106223 := (sr 1 106223 159335 (by norm_num) (by norm_num) (sr 1 159335 239003 (by norm_num) (by norm_num) (sr 1 239003 358505 (by norm_num) (by norm_num) (sr 2 358505 268879 (by norm_num) (by norm_num) (sr 1 268879 403319 (by norm_num) (by norm_num) (sr 1 403319 604979 (by norm_num) (by norm_num) (sr 1 604979 907469 (by norm_num) (by norm_num) (sr 3 907469 340301 (by norm_num) (by norm_num) (sr 3 340301 127613 (by norm_num) (by norm_num) (sr 3 127613 47855 (by norm_num) (by norm_num) (B 47855 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R106227 : Reach 106227 := (sr 1 106227 159341 (by norm_num) (by norm_num) (sr 3 159341 59753 (by norm_num) (by norm_num) (B 59753 (by norm_num) (by norm_num) (by norm_num))))
theorem R106231 : Reach 106231 := (sr 1 106231 159347 (by norm_num) (by norm_num) (sr 1 159347 239021 (by norm_num) (by norm_num) (sr 3 239021 89633 (by norm_num) (by norm_num) (B 89633 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106235 : Reach 106235 := (sr 1 106235 159353 (by norm_num) (by norm_num) (sr 2 159353 119515 (by norm_num) (by norm_num) (sr 1 119515 179273 (by norm_num) (by norm_num) (sr 2 179273 134455 (by norm_num) (by norm_num) (sr 1 134455 201683 (by norm_num) (by norm_num) (sr 1 201683 302525 (by norm_num) (by norm_num) (sr 3 302525 113447 (by norm_num) (by norm_num) (sr 1 113447 170171 (by norm_num) (by norm_num) (sr 1 170171 255257 (by norm_num) (by norm_num) (sr 2 255257 191443 (by norm_num) (by norm_num) (sr 1 191443 287165 (by norm_num) (by norm_num) (sr 3 287165 107687 (by norm_num) (by norm_num) (sr 1 107687 161531 (by norm_num) (by norm_num) (sr 1 161531 242297 (by norm_num) (by norm_num) (sr 2 242297 181723 (by norm_num) (by norm_num) (sr 1 181723 272585 (by norm_num) (by norm_num) (sr 2 272585 204439 (by norm_num) (by norm_num) (sr 1 204439 306659 (by norm_num) (by norm_num) (sr 1 306659 459989 (by norm_num) (by norm_num) (sr 7 459989 10781 (by norm_num) (by norm_num) (B 10781 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))
theorem R106239 : Reach 106239 := (sr 1 106239 159359 (by norm_num) (by norm_num) (sr 1 159359 239039 (by norm_num) (by norm_num) (sr 1 239039 358559 (by norm_num) (by norm_num) (sr 1 358559 537839 (by norm_num) (by norm_num) (sr 1 537839 806759 (by norm_num) (by norm_num) (sr 1 806759 1210139 (by norm_num) (by norm_num) (sr 1 1210139 1815209 (by norm_num) (by norm_num) (sr 2 1815209 1361407 (by norm_num) (by norm_num) (sr 1 1361407 2042111 (by norm_num) (by norm_num) (sr 1 2042111 3063167 (by norm_num) (by norm_num) (sr 1 3063167 4594751 (by norm_num) (by norm_num) (sr 1 4594751 6892127 (by norm_num) (by norm_num) (sr 1 6892127 10338191 (by norm_num) (by norm_num) (sr 1 10338191 15507287 (by norm_num) (by norm_num) (sr 1 15507287 23260931 (by norm_num) (by norm_num) (sr 1 23260931 34891397 (by norm_num) (by norm_num) (sr 4 34891397 6542137 (by norm_num) (by norm_num) (sr 2 6542137 4906603 (by norm_num) (by norm_num) (sr 1 4906603 7359905 (by norm_num) (by norm_num) (sr 2 7359905 5519929 (by norm_num) (by norm_num) (sr 2 5519929 4139947 (by norm_num) (by norm_num) (sr 1 4139947 6209921 (by norm_num) (by norm_num) (sr 2 6209921 4657441 (by norm_num) (by norm_num) (sr 2 4657441 3493081 (by norm_num) (by norm_num) (sr 2 3493081 2619811 (by norm_num) (by norm_num) (sr 1 2619811 3929717 (by norm_num) (by norm_num) (sr 5 3929717 368411 (by norm_num) (by norm_num) (sr 1 368411 552617 (by norm_num) (by norm_num) (sr 2 552617 414463 (by norm_num) (by norm_num) (sr 1 414463 621695 (by norm_num) (by norm_num) (sr 1 621695 932543 (by norm_num) (by norm_num) (sr 1 932543 1398815 (by norm_num) (by norm_num) (sr 1 1398815 2098223 (by norm_num) (by norm_num) (sr 1 2098223 3147335 (by norm_num) (by norm_num) (sr 1 3147335 4721003 (by norm_num) (by norm_num) (sr 1 4721003 7081505 (by norm_num) (by norm_num) (sr 2 7081505 5311129 (by norm_num) (by norm_num) (sr 2 5311129 3983347 (by norm_num) (by norm_num) (sr 1 3983347 5975021 (by norm_num) (by norm_num) (sr 3 5975021 2240633 (by norm_num) (by norm_num) (sr 2 2240633 1680475 (by norm_num) (by norm_num) (sr 1 1680475 2520713 (by norm_num) (by norm_num) (sr 2 2520713 1890535 (by norm_num) (by norm_num) (sr 1 1890535 2835803 (by norm_num) (by norm_num) (sr 1 2835803 4253705 (by norm_num) (by norm_num) (sr 2 4253705 3190279 (by norm_num) (by norm_num) (sr 1 3190279 4785419 (by norm_num) (by norm_num) (sr 1 4785419 7178129 (by norm_num) (by norm_num) (sr 2 7178129 5383597 (by norm_num) (by norm_num) (sr 3 5383597 2018849 (by norm_num) (by norm_num) (sr 2 2018849 1514137 (by norm_num) (by norm_num) (sr 2 1514137 1135603 (by norm_num) (by norm_num) (sr 1 1135603 1703405 (by norm_num) (by norm_num) (sr 3 1703405 638777 (by norm_num) (by norm_num) (sr 2 638777 479083 (by norm_num) (by norm_num) (sr 1 479083 718625 (by norm_num) (by norm_num) (sr 2 718625 538969 (by norm_num) (by norm_num) (sr 2 538969 404227 (by norm_num) (by norm_num) (sr 1 404227 606341 (by norm_num) (by norm_num) (sr 4 606341 113689 (by norm_num) (by norm_num) (sr 2 113689 85267 (by norm_num) (by norm_num) (B 85267 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem R106243 : Reach 106243 := (sr 1 106243 159365 (by norm_num) (by norm_num) (sr 4 159365 29881 (by norm_num) (by norm_num) (B 29881 (by norm_num) (by norm_num) (by norm_num))))
theorem R106247 : Reach 106247 := (sr 1 106247 159371 (by norm_num) (by norm_num) (sr 1 159371 239057 (by norm_num) (by norm_num) (sr 2 239057 179293 (by norm_num) (by norm_num) (sr 3 179293 67235 (by norm_num) (by norm_num) (B 67235 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106251 : Reach 106251 := (sr 1 106251 159377 (by norm_num) (by norm_num) (sr 2 159377 119533 (by norm_num) (by norm_num) (sr 3 119533 44825 (by norm_num) (by norm_num) (B 44825 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106255 : Reach 106255 := (sr 1 106255 159383 (by norm_num) (by norm_num) (sr 1 159383 239075 (by norm_num) (by norm_num) (sr 1 239075 358613 (by norm_num) (by norm_num) (sr 7 358613 8405 (by norm_num) (by norm_num) (B 8405 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106259 : Reach 106259 := (sr 1 106259 159389 (by norm_num) (by norm_num) (sr 3 159389 59771 (by norm_num) (by norm_num) (B 59771 (by norm_num) (by norm_num) (by norm_num))))
theorem R106263 : Reach 106263 := (sr 1 106263 159395 (by norm_num) (by norm_num) (sr 1 159395 239093 (by norm_num) (by norm_num) (sr 5 239093 22415 (by norm_num) (by norm_num) (B 22415 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106267 : Reach 106267 := (sr 1 106267 159401 (by norm_num) (by norm_num) (sr 2 159401 119551 (by norm_num) (by norm_num) (sr 1 119551 179327 (by norm_num) (by norm_num) (sr 1 179327 268991 (by norm_num) (by norm_num) (sr 1 268991 403487 (by norm_num) (by norm_num) (sr 1 403487 605231 (by norm_num) (by norm_num) (sr 1 605231 907847 (by norm_num) (by norm_num) (sr 1 907847 1361771 (by norm_num) (by norm_num) (sr 1 1361771 2042657 (by norm_num) (by norm_num) (sr 2 2042657 1531993 (by norm_num) (by norm_num) (sr 2 1531993 1148995 (by norm_num) (by norm_num) (sr 1 1148995 1723493 (by norm_num) (by norm_num) (sr 4 1723493 323155 (by norm_num) (by norm_num) (sr 1 323155 484733 (by norm_num) (by norm_num) (sr 3 484733 181775 (by norm_num) (by norm_num) (sr 1 181775 272663 (by norm_num) (by norm_num) (sr 1 272663 408995 (by norm_num) (by norm_num) (sr 1 408995 613493 (by norm_num) (by norm_num) (sr 5 613493 57515 (by norm_num) (by norm_num) (B 57515 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))
theorem R106271 : Reach 106271 := (sr 1 106271 159407 (by norm_num) (by norm_num) (sr 1 159407 239111 (by norm_num) (by norm_num) (sr 1 239111 358667 (by norm_num) (by norm_num) (sr 1 358667 538001 (by norm_num) (by norm_num) (sr 2 538001 403501 (by norm_num) (by norm_num) (sr 3 403501 151313 (by norm_num) (by norm_num) (sr 2 151313 113485 (by norm_num) (by norm_num) (sr 3 113485 42557 (by norm_num) (by norm_num) (B 42557 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R106275 : Reach 106275 := (sr 1 106275 159413 (by norm_num) (by norm_num) (sr 5 159413 14945 (by norm_num) (by norm_num) (B 14945 (by norm_num) (by norm_num) (by norm_num))))
theorem R106279 : Reach 106279 := (sr 1 106279 159419 (by norm_num) (by norm_num) (sr 1 159419 239129 (by norm_num) (by norm_num) (sr 2 239129 179347 (by norm_num) (by norm_num) (sr 1 179347 269021 (by norm_num) (by norm_num) (sr 3 269021 100883 (by norm_num) (by norm_num) R100883)))))
theorem R106283 : Reach 106283 := (sr 1 106283 159425 (by norm_num) (by norm_num) (sr 2 159425 119569 (by norm_num) (by norm_num) (sr 2 119569 89677 (by norm_num) (by norm_num) (B 89677 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106287 : Reach 106287 := (sr 1 106287 159431 (by norm_num) (by norm_num) (sr 1 159431 239147 (by norm_num) (by norm_num) (sr 1 239147 358721 (by norm_num) (by norm_num) (sr 2 358721 269041 (by norm_num) (by norm_num) (sr 2 269041 201781 (by norm_num) (by norm_num) (sr 5 201781 18917 (by norm_num) (by norm_num) (B 18917 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106291 : Reach 106291 := (sr 1 106291 159437 (by norm_num) (by norm_num) (sr 3 159437 59789 (by norm_num) (by norm_num) (B 59789 (by norm_num) (by norm_num) (by norm_num))))
theorem R106295 : Reach 106295 := (sr 1 106295 159443 (by norm_num) (by norm_num) (sr 1 159443 239165 (by norm_num) (by norm_num) (sr 3 239165 89687 (by norm_num) (by norm_num) (B 89687 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106299 : Reach 106299 := (sr 1 106299 159449 (by norm_num) (by norm_num) (sr 2 159449 119587 (by norm_num) (by norm_num) (sr 1 119587 179381 (by norm_num) (by norm_num) (sr 5 179381 16817 (by norm_num) (by norm_num) (B 16817 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106303 : Reach 106303 := (sr 1 106303 159455 (by norm_num) (by norm_num) (sr 1 159455 239183 (by norm_num) (by norm_num) (sr 1 239183 358775 (by norm_num) (by norm_num) (sr 1 358775 538163 (by norm_num) (by norm_num) (sr 1 538163 807245 (by norm_num) (by norm_num) (sr 3 807245 302717 (by norm_num) (by norm_num) (sr 3 302717 113519 (by norm_num) (by norm_num) (sr 1 113519 170279 (by norm_num) (by norm_num) (sr 1 170279 255419 (by norm_num) (by norm_num) (sr 1 255419 383129 (by norm_num) (by norm_num) (sr 2 383129 287347 (by norm_num) (by norm_num) (sr 1 287347 431021 (by norm_num) (by norm_num) (sr 3 431021 161633 (by norm_num) (by norm_num) (sr 2 161633 121225 (by norm_num) (by norm_num) (sr 2 121225 90919 (by norm_num) (by norm_num) (B 90919 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R106307 : Reach 106307 := (sr 1 106307 159461 (by norm_num) (by norm_num) (sr 4 159461 29899 (by norm_num) (by norm_num) (B 29899 (by norm_num) (by norm_num) (by norm_num))))
theorem R106311 : Reach 106311 := (sr 1 106311 159467 (by norm_num) (by norm_num) (sr 1 159467 239201 (by norm_num) (by norm_num) (sr 2 239201 179401 (by norm_num) (by norm_num) (sr 2 179401 134551 (by norm_num) (by norm_num) (sr 1 134551 201827 (by norm_num) (by norm_num) (sr 1 201827 302741 (by norm_num) (by norm_num) (sr 6 302741 14191 (by norm_num) (by norm_num) (B 14191 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R106315 : Reach 106315 := (sr 1 106315 159473 (by norm_num) (by norm_num) (sr 2 159473 119605 (by norm_num) (by norm_num) (sr 5 119605 11213 (by norm_num) (by norm_num) (B 11213 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106319 : Reach 106319 := (sr 1 106319 159479 (by norm_num) (by norm_num) (sr 1 159479 239219 (by norm_num) (by norm_num) (sr 1 239219 358829 (by norm_num) (by norm_num) (sr 3 358829 134561 (by norm_num) (by norm_num) (sr 2 134561 100921 (by norm_num) (by norm_num) (sr 2 100921 75691 (by norm_num) (by norm_num) (B 75691 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106323 : Reach 106323 := (sr 1 106323 159485 (by norm_num) (by norm_num) (sr 3 159485 59807 (by norm_num) (by norm_num) (B 59807 (by norm_num) (by norm_num) (by norm_num))))
theorem R106327 : Reach 106327 := (sr 1 106327 159491 (by norm_num) (by norm_num) (sr 1 159491 239237 (by norm_num) (by norm_num) (sr 4 239237 44857 (by norm_num) (by norm_num) (B 44857 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106331 : Reach 106331 := (sr 1 106331 159497 (by norm_num) (by norm_num) (sr 2 159497 119623 (by norm_num) (by norm_num) (sr 1 119623 179435 (by norm_num) (by norm_num) (sr 1 179435 269153 (by norm_num) (by norm_num) (sr 2 269153 201865 (by norm_num) (by norm_num) (sr 2 201865 151399 (by norm_num) (by norm_num) (sr 1 151399 227099 (by norm_num) (by norm_num) (sr 1 227099 340649 (by norm_num) (by norm_num) (sr 2 340649 255487 (by norm_num) (by norm_num) (sr 1 255487 383231 (by norm_num) (by norm_num) (sr 1 383231 574847 (by norm_num) (by norm_num) (sr 1 574847 862271 (by norm_num) (by norm_num) (sr 1 862271 1293407 (by norm_num) (by norm_num) (sr 1 1293407 1940111 (by norm_num) (by norm_num) (sr 1 1940111 2910167 (by norm_num) (by norm_num) (sr 1 2910167 4365251 (by norm_num) (by norm_num) (sr 1 4365251 6547877 (by norm_num) (by norm_num) (sr 4 6547877 1227727 (by norm_num) (by norm_num) (sr 1 1227727 1841591 (by norm_num) (by norm_num) (sr 1 1841591 2762387 (by norm_num) (by norm_num) (sr 1 2762387 4143581 (by norm_num) (by norm_num) (sr 3 4143581 1553843 (by norm_num) (by norm_num) (sr 1 1553843 2330765 (by norm_num) (by norm_num) (sr 3 2330765 874037 (by norm_num) (by norm_num) (sr 5 874037 81941 (by norm_num) (by norm_num) (B 81941 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))
theorem R106335 : Reach 106335 := (sr 1 106335 159503 (by norm_num) (by norm_num) (sr 1 159503 239255 (by norm_num) (by norm_num) (sr 1 239255 358883 (by norm_num) (by norm_num) (sr 1 358883 538325 (by norm_num) (by norm_num) (sr 7 538325 12617 (by norm_num) (by norm_num) (B 12617 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R106339 : Reach 106339 := (sr 1 106339 159509 (by norm_num) (by norm_num) (sr 6 159509 7477 (by norm_num) (by norm_num) (B 7477 (by norm_num) (by norm_num) (by norm_num))))
theorem R106343 : Reach 106343 := (sr 1 106343 159515 (by norm_num) (by norm_num) (sr 1 159515 239273 (by norm_num) (by norm_num) (sr 2 239273 179455 (by norm_num) (by norm_num) (sr 1 179455 269183 (by norm_num) (by norm_num) (sr 1 269183 403775 (by norm_num) (by norm_num) (sr 1 403775 605663 (by norm_num) (by norm_num) (sr 1 605663 908495 (by norm_num) (by norm_num) (sr 1 908495 1362743 (by norm_num) (by norm_num) (sr 1 1362743 2044115 (by norm_num) (by norm_num) (sr 1 2044115 3066173 (by norm_num) (by norm_num) (sr 3 3066173 1149815 (by norm_num) (by norm_num) (sr 1 1149815 1724723 (by norm_num) (by norm_num) (sr 1 1724723 2587085 (by norm_num) (by norm_num) (sr 3 2587085 970157 (by norm_num) (by norm_num) (sr 3 970157 363809 (by norm_num) (by norm_num) (sr 2 363809 272857 (by norm_num) (by norm_num) (sr 2 272857 204643 (by norm_num) (by norm_num) (sr 1 204643 306965 (by norm_num) (by norm_num) (sr 6 306965 14389 (by norm_num) (by norm_num) (B 14389 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))
theorem R106347 : Reach 106347 := (sr 1 106347 159521 (by norm_num) (by norm_num) (sr 2 159521 119641 (by norm_num) (by norm_num) (sr 2 119641 89731 (by norm_num) (by norm_num) (B 89731 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106351 : Reach 106351 := (sr 1 106351 159527 (by norm_num) (by norm_num) (sr 1 159527 239291 (by norm_num) (by norm_num) (sr 1 239291 358937 (by norm_num) (by norm_num) (sr 2 358937 269203 (by norm_num) (by norm_num) (sr 1 269203 403805 (by norm_num) (by norm_num) (sr 3 403805 151427 (by norm_num) (by norm_num) (sr 1 151427 227141 (by norm_num) (by norm_num) (sr 4 227141 42589 (by norm_num) (by norm_num) (B 42589 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R106355 : Reach 106355 := (sr 1 106355 159533 (by norm_num) (by norm_num) (sr 3 159533 59825 (by norm_num) (by norm_num) (B 59825 (by norm_num) (by norm_num) (by norm_num))))
theorem R106359 : Reach 106359 := (sr 1 106359 159539 (by norm_num) (by norm_num) (sr 1 159539 239309 (by norm_num) (by norm_num) (sr 3 239309 89741 (by norm_num) (by norm_num) (B 89741 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106363 : Reach 106363 := (sr 1 106363 159545 (by norm_num) (by norm_num) (sr 2 159545 119659 (by norm_num) (by norm_num) (sr 1 119659 179489 (by norm_num) (by norm_num) (sr 2 179489 134617 (by norm_num) (by norm_num) (sr 2 134617 100963 (by norm_num) (by norm_num) R100963)))))
theorem R106367 : Reach 106367 := (sr 1 106367 159551 (by norm_num) (by norm_num) (sr 1 159551 239327 (by norm_num) (by norm_num) (sr 1 239327 358991 (by norm_num) (by norm_num) (sr 1 358991 538487 (by norm_num) (by norm_num) (sr 1 538487 807731 (by norm_num) (by norm_num) (sr 1 807731 1211597 (by norm_num) (by norm_num) (sr 3 1211597 454349 (by norm_num) (by norm_num) (sr 3 454349 170381 (by norm_num) (by norm_num) (sr 3 170381 63893 (by norm_num) (by norm_num) (B 63893 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R106371 : Reach 106371 := (sr 1 106371 159557 (by norm_num) (by norm_num) (sr 4 159557 29917 (by norm_num) (by norm_num) (B 29917 (by norm_num) (by norm_num) (by norm_num))))
theorem R106375 : Reach 106375 := (sr 1 106375 159563 (by norm_num) (by norm_num) (sr 1 159563 239345 (by norm_num) (by norm_num) (sr 2 239345 179509 (by norm_num) (by norm_num) (sr 5 179509 16829 (by norm_num) (by norm_num) (B 16829 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106379 : Reach 106379 := (sr 1 106379 159569 (by norm_num) (by norm_num) (sr 2 159569 119677 (by norm_num) (by norm_num) (sr 3 119677 44879 (by norm_num) (by norm_num) (B 44879 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106383 : Reach 106383 := (sr 1 106383 159575 (by norm_num) (by norm_num) (sr 1 159575 239363 (by norm_num) (by norm_num) (sr 1 239363 359045 (by norm_num) (by norm_num) (sr 4 359045 67321 (by norm_num) (by norm_num) (B 67321 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106387 : Reach 106387 := (sr 1 106387 159581 (by norm_num) (by norm_num) (sr 3 159581 59843 (by norm_num) (by norm_num) (B 59843 (by norm_num) (by norm_num) (by norm_num))))
theorem R106391 : Reach 106391 := (sr 1 106391 159587 (by norm_num) (by norm_num) (sr 1 159587 239381 (by norm_num) (by norm_num) (sr 6 239381 11221 (by norm_num) (by norm_num) (B 11221 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106395 : Reach 106395 := (sr 1 106395 159593 (by norm_num) (by norm_num) (sr 2 159593 119695 (by norm_num) (by norm_num) (sr 1 119695 179543 (by norm_num) (by norm_num) (sr 1 179543 269315 (by norm_num) (by norm_num) (sr 1 269315 403973 (by norm_num) (by norm_num) (sr 4 403973 75745 (by norm_num) (by norm_num) (B 75745 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106399 : Reach 106399 := (sr 1 106399 159599 (by norm_num) (by norm_num) (sr 1 159599 239399 (by norm_num) (by norm_num) (sr 1 239399 359099 (by norm_num) (by norm_num) (sr 1 359099 538649 (by norm_num) (by norm_num) (sr 2 538649 403987 (by norm_num) (by norm_num) (sr 1 403987 605981 (by norm_num) (by norm_num) (sr 3 605981 227243 (by norm_num) (by norm_num) (sr 1 227243 340865 (by norm_num) (by norm_num) (sr 2 340865 255649 (by norm_num) (by norm_num) (sr 2 255649 191737 (by norm_num) (by norm_num) (sr 2 191737 143803 (by norm_num) (by norm_num) (sr 1 143803 215705 (by norm_num) (by norm_num) (sr 2 215705 161779 (by norm_num) (by norm_num) (sr 1 161779 242669 (by norm_num) (by norm_num) (sr 3 242669 91001 (by norm_num) (by norm_num) (B 91001 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R106403 : Reach 106403 := (sr 1 106403 159605 (by norm_num) (by norm_num) (sr 5 159605 14963 (by norm_num) (by norm_num) (B 14963 (by norm_num) (by norm_num) (by norm_num))))
theorem R106407 : Reach 106407 := (sr 1 106407 159611 (by norm_num) (by norm_num) (sr 1 159611 239417 (by norm_num) (by norm_num) (sr 2 239417 179563 (by norm_num) (by norm_num) (sr 1 179563 269345 (by norm_num) (by norm_num) (sr 2 269345 202009 (by norm_num) (by norm_num) (sr 2 202009 151507 (by norm_num) (by norm_num) (sr 1 151507 227261 (by norm_num) (by norm_num) (sr 3 227261 85223 (by norm_num) (by norm_num) (B 85223 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R106411 : Reach 106411 := (sr 1 106411 159617 (by norm_num) (by norm_num) (sr 2 159617 119713 (by norm_num) (by norm_num) (sr 2 119713 89785 (by norm_num) (by norm_num) (B 89785 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106415 : Reach 106415 := (sr 1 106415 159623 (by norm_num) (by norm_num) (sr 1 159623 239435 (by norm_num) (by norm_num) (sr 1 239435 359153 (by norm_num) (by norm_num) (sr 2 359153 269365 (by norm_num) (by norm_num) (sr 5 269365 25253 (by norm_num) (by norm_num) (B 25253 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R106419 : Reach 106419 := (sr 1 106419 159629 (by norm_num) (by norm_num) (sr 3 159629 59861 (by norm_num) (by norm_num) (B 59861 (by norm_num) (by norm_num) (by norm_num))))
theorem R106423 : Reach 106423 := (sr 1 106423 159635 (by norm_num) (by norm_num) (sr 1 159635 239453 (by norm_num) (by norm_num) (sr 3 239453 89795 (by norm_num) (by norm_num) (B 89795 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106427 : Reach 106427 := (sr 1 106427 159641 (by norm_num) (by norm_num) (sr 2 159641 119731 (by norm_num) (by norm_num) (sr 1 119731 179597 (by norm_num) (by norm_num) (sr 3 179597 67349 (by norm_num) (by norm_num) (B 67349 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106431 : Reach 106431 := (sr 1 106431 159647 (by norm_num) (by norm_num) (sr 1 159647 239471 (by norm_num) (by norm_num) (sr 1 239471 359207 (by norm_num) (by norm_num) (sr 1 359207 538811 (by norm_num) (by norm_num) (sr 1 538811 808217 (by norm_num) (by norm_num) (sr 2 808217 606163 (by norm_num) (by norm_num) (sr 1 606163 909245 (by norm_num) (by norm_num) (sr 3 909245 340967 (by norm_num) (by norm_num) (sr 1 340967 511451 (by norm_num) (by norm_num) (sr 1 511451 767177 (by norm_num) (by norm_num) (sr 2 767177 575383 (by norm_num) (by norm_num) (sr 1 575383 863075 (by norm_num) (by norm_num) (sr 1 863075 1294613 (by norm_num) (by norm_num) (sr 6 1294613 60685 (by norm_num) (by norm_num) (B 60685 (by norm_num) (by norm_num) (by norm_num))))))))))))))))
theorem R106435 : Reach 106435 := (sr 1 106435 159653 (by norm_num) (by norm_num) (sr 4 159653 29935 (by norm_num) (by norm_num) (B 29935 (by norm_num) (by norm_num) (by norm_num))))
theorem R106439 : Reach 106439 := (sr 1 106439 159659 (by norm_num) (by norm_num) (sr 1 159659 239489 (by norm_num) (by norm_num) (sr 2 239489 179617 (by norm_num) (by norm_num) (sr 2 179617 134713 (by norm_num) (by norm_num) (sr 2 134713 101035 (by norm_num) (by norm_num) R101035)))))
theorem R106443 : Reach 106443 := (sr 1 106443 159665 (by norm_num) (by norm_num) (sr 2 159665 119749 (by norm_num) (by norm_num) (sr 4 119749 22453 (by norm_num) (by norm_num) (B 22453 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106447 : Reach 106447 := (sr 1 106447 159671 (by norm_num) (by norm_num) (sr 1 159671 239507 (by norm_num) (by norm_num) (sr 1 239507 359261 (by norm_num) (by norm_num) (sr 3 359261 134723 (by norm_num) (by norm_num) (sr 1 134723 202085 (by norm_num) (by norm_num) (sr 4 202085 37891 (by norm_num) (by norm_num) (B 37891 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106451 : Reach 106451 := (sr 1 106451 159677 (by norm_num) (by norm_num) (sr 3 159677 59879 (by norm_num) (by norm_num) (B 59879 (by norm_num) (by norm_num) (by norm_num))))
theorem R106455 : Reach 106455 := (sr 1 106455 159683 (by norm_num) (by norm_num) (sr 1 159683 239525 (by norm_num) (by norm_num) (sr 4 239525 44911 (by norm_num) (by norm_num) (B 44911 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106459 : Reach 106459 := (sr 1 106459 159689 (by norm_num) (by norm_num) (sr 2 159689 119767 (by norm_num) (by norm_num) (sr 1 119767 179651 (by norm_num) (by norm_num) (sr 1 179651 269477 (by norm_num) (by norm_num) (sr 4 269477 50527 (by norm_num) (by norm_num) (B 50527 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R106463 : Reach 106463 := (sr 1 106463 159695 (by norm_num) (by norm_num) (sr 1 159695 239543 (by norm_num) (by norm_num) (sr 1 239543 359315 (by norm_num) (by norm_num) (sr 1 359315 538973 (by norm_num) (by norm_num) (sr 3 538973 202115 (by norm_num) (by norm_num) (sr 1 202115 303173 (by norm_num) (by norm_num) (sr 4 303173 56845 (by norm_num) (by norm_num) (B 56845 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R106467 : Reach 106467 := (sr 1 106467 159701 (by norm_num) (by norm_num) (sr 7 159701 3743 (by norm_num) (by norm_num) (B 3743 (by norm_num) (by norm_num) (by norm_num))))
theorem R106471 : Reach 106471 := (sr 1 106471 159707 (by norm_num) (by norm_num) (sr 1 159707 239561 (by norm_num) (by norm_num) (sr 2 239561 179671 (by norm_num) (by norm_num) (sr 1 179671 269507 (by norm_num) (by norm_num) (sr 1 269507 404261 (by norm_num) (by norm_num) (sr 4 404261 75799 (by norm_num) (by norm_num) (B 75799 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106475 : Reach 106475 := (sr 1 106475 159713 (by norm_num) (by norm_num) (sr 2 159713 119785 (by norm_num) (by norm_num) (sr 2 119785 89839 (by norm_num) (by norm_num) (B 89839 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106479 : Reach 106479 := (sr 1 106479 159719 (by norm_num) (by norm_num) (sr 1 159719 239579 (by norm_num) (by norm_num) (sr 1 239579 359369 (by norm_num) (by norm_num) (sr 2 359369 269527 (by norm_num) (by norm_num) (sr 1 269527 404291 (by norm_num) (by norm_num) (sr 1 404291 606437 (by norm_num) (by norm_num) (sr 4 606437 113707 (by norm_num) (by norm_num) (sr 1 113707 170561 (by norm_num) (by norm_num) (sr 2 170561 127921 (by norm_num) (by norm_num) (sr 2 127921 95941 (by norm_num) (by norm_num) (B 95941 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R106483 : Reach 106483 := (sr 1 106483 159725 (by norm_num) (by norm_num) (sr 3 159725 59897 (by norm_num) (by norm_num) (B 59897 (by norm_num) (by norm_num) (by norm_num))))
theorem R106487 : Reach 106487 := (sr 1 106487 159731 (by norm_num) (by norm_num) (sr 1 159731 239597 (by norm_num) (by norm_num) (sr 3 239597 89849 (by norm_num) (by norm_num) (B 89849 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106491 : Reach 106491 := (sr 1 106491 159737 (by norm_num) (by norm_num) (sr 2 159737 119803 (by norm_num) (by norm_num) (sr 1 119803 179705 (by norm_num) (by norm_num) (sr 2 179705 134779 (by norm_num) (by norm_num) (sr 1 134779 202169 (by norm_num) (by norm_num) (sr 2 202169 151627 (by norm_num) (by norm_num) (sr 1 151627 227441 (by norm_num) (by norm_num) (sr 2 227441 170581 (by norm_num) (by norm_num) (sr 8 170581 1999 (by norm_num) (by norm_num) (B 1999 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R106495 : Reach 106495 := (sr 1 106495 159743 (by norm_num) (by norm_num) (sr 1 159743 239615 (by norm_num) (by norm_num) (sr 1 239615 359423 (by norm_num) (by norm_num) (sr 1 359423 539135 (by norm_num) (by norm_num) (sr 1 539135 808703 (by norm_num) (by norm_num) (sr 1 808703 1213055 (by norm_num) (by norm_num) (sr 1 1213055 1819583 (by norm_num) (by norm_num) (sr 1 1819583 2729375 (by norm_num) (by norm_num) (sr 1 2729375 4094063 (by norm_num) (by norm_num) (sr 1 4094063 6141095 (by norm_num) (by norm_num) (sr 1 6141095 9211643 (by norm_num) (by norm_num) (sr 1 9211643 13817465 (by norm_num) (by norm_num) (sr 2 13817465 10363099 (by norm_num) (by norm_num) (sr 1 10363099 15544649 (by norm_num) (by norm_num) (sr 2 15544649 11658487 (by norm_num) (by norm_num) (sr 1 11658487 17487731 (by norm_num) (by norm_num) (sr 1 17487731 26231597 (by norm_num) (by norm_num) (sr 3 26231597 9836849 (by norm_num) (by norm_num) (sr 2 9836849 7377637 (by norm_num) (by norm_num) (sr 4 7377637 1383307 (by norm_num) (by norm_num) (sr 1 1383307 2074961 (by norm_num) (by norm_num) (sr 2 2074961 1556221 (by norm_num) (by norm_num) (sr 3 1556221 583583 (by norm_num) (by norm_num) (sr 1 583583 875375 (by norm_num) (by norm_num) (sr 1 875375 1313063 (by norm_num) (by norm_num) (sr 1 1313063 1969595 (by norm_num) (by norm_num) (sr 1 1969595 2954393 (by norm_num) (by norm_num) (sr 2 2954393 2215795 (by norm_num) (by norm_num) (sr 1 2215795 3323693 (by norm_num) (by norm_num) (sr 3 3323693 1246385 (by norm_num) (by norm_num) (sr 2 1246385 934789 (by norm_num) (by norm_num) (sr 4 934789 175273 (by norm_num) (by norm_num) (sr 2 175273 131455 (by norm_num) (by norm_num) (sr 1 131455 197183 (by norm_num) (by norm_num) (sr 1 197183 295775 (by norm_num) (by norm_num) (sr 1 295775 443663 (by norm_num) (by norm_num) (sr 1 443663 665495 (by norm_num) (by norm_num) (sr 1 665495 998243 (by norm_num) (by norm_num) (sr 1 998243 1497365 (by norm_num) (by norm_num) (sr 6 1497365 70189 (by norm_num) (by norm_num) (B 70189 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))))))))))))))
theorem R106499 : Reach 106499 := (sr 1 106499 159749 (by norm_num) (by norm_num) (sr 4 159749 29953 (by norm_num) (by norm_num) (B 29953 (by norm_num) (by norm_num) (by norm_num))))
theorem R106503 : Reach 106503 := (sr 1 106503 159755 (by norm_num) (by norm_num) (sr 1 159755 239633 (by norm_num) (by norm_num) (sr 2 239633 179725 (by norm_num) (by norm_num) (sr 3 179725 67397 (by norm_num) (by norm_num) (B 67397 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106507 : Reach 106507 := (sr 1 106507 159761 (by norm_num) (by norm_num) (sr 2 159761 119821 (by norm_num) (by norm_num) (sr 3 119821 44933 (by norm_num) (by norm_num) (B 44933 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106511 : Reach 106511 := (sr 1 106511 159767 (by norm_num) (by norm_num) (sr 1 159767 239651 (by norm_num) (by norm_num) (sr 1 239651 359477 (by norm_num) (by norm_num) (sr 5 359477 33701 (by norm_num) (by norm_num) (B 33701 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106515 : Reach 106515 := (sr 1 106515 159773 (by norm_num) (by norm_num) (sr 3 159773 59915 (by norm_num) (by norm_num) (B 59915 (by norm_num) (by norm_num) (by norm_num))))
theorem R106519 : Reach 106519 := (sr 1 106519 159779 (by norm_num) (by norm_num) (sr 1 159779 239669 (by norm_num) (by norm_num) (sr 5 239669 22469 (by norm_num) (by norm_num) (B 22469 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106523 : Reach 106523 := (sr 1 106523 159785 (by norm_num) (by norm_num) (sr 2 159785 119839 (by norm_num) (by norm_num) (sr 1 119839 179759 (by norm_num) (by norm_num) (sr 1 179759 269639 (by norm_num) (by norm_num) (sr 1 269639 404459 (by norm_num) (by norm_num) (sr 1 404459 606689 (by norm_num) (by norm_num) (sr 2 606689 455017 (by norm_num) (by norm_num) (sr 2 455017 341263 (by norm_num) (by norm_num) (sr 1 341263 511895 (by norm_num) (by norm_num) (sr 1 511895 767843 (by norm_num) (by norm_num) (sr 1 767843 1151765 (by norm_num) (by norm_num) (sr 6 1151765 53989 (by norm_num) (by norm_num) (B 53989 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R106527 : Reach 106527 := (sr 1 106527 159791 (by norm_num) (by norm_num) (sr 1 159791 239687 (by norm_num) (by norm_num) (sr 1 239687 359531 (by norm_num) (by norm_num) (sr 1 359531 539297 (by norm_num) (by norm_num) (sr 2 539297 404473 (by norm_num) (by norm_num) (sr 2 404473 303355 (by norm_num) (by norm_num) (sr 1 303355 455033 (by norm_num) (by norm_num) (sr 2 455033 341275 (by norm_num) (by norm_num) (sr 1 341275 511913 (by norm_num) (by norm_num) (sr 2 511913 383935 (by norm_num) (by norm_num) (sr 1 383935 575903 (by norm_num) (by norm_num) (sr 1 575903 863855 (by norm_num) (by norm_num) (sr 1 863855 1295783 (by norm_num) (by norm_num) (sr 1 1295783 1943675 (by norm_num) (by norm_num) (sr 1 1943675 2915513 (by norm_num) (by norm_num) (sr 2 2915513 2186635 (by norm_num) (by norm_num) (sr 1 2186635 3279953 (by norm_num) (by norm_num) (sr 2 3279953 2459965 (by norm_num) (by norm_num) (sr 3 2459965 922487 (by norm_num) (by norm_num) (sr 1 922487 1383731 (by norm_num) (by norm_num) (sr 1 1383731 2075597 (by norm_num) (by norm_num) (sr 3 2075597 778349 (by norm_num) (by norm_num) (sr 3 778349 291881 (by norm_num) (by norm_num) (sr 2 291881 218911 (by norm_num) (by norm_num) (sr 1 218911 328367 (by norm_num) (by norm_num) (sr 1 328367 492551 (by norm_num) (by norm_num) (sr 1 492551 738827 (by norm_num) (by norm_num) (sr 1 738827 1108241 (by norm_num) (by norm_num) (sr 2 1108241 831181 (by norm_num) (by norm_num) (sr 3 831181 311693 (by norm_num) (by norm_num) (sr 3 311693 116885 (by norm_num) (by norm_num) (sr 6 116885 5479 (by norm_num) (by norm_num) (B 5479 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))))))
theorem R106531 : Reach 106531 := (sr 1 106531 159797 (by norm_num) (by norm_num) (sr 5 159797 14981 (by norm_num) (by norm_num) (B 14981 (by norm_num) (by norm_num) (by norm_num))))
theorem R106535 : Reach 106535 := (sr 1 106535 159803 (by norm_num) (by norm_num) (sr 1 159803 239705 (by norm_num) (by norm_num) (sr 2 239705 179779 (by norm_num) (by norm_num) (sr 1 179779 269669 (by norm_num) (by norm_num) (sr 4 269669 50563 (by norm_num) (by norm_num) (B 50563 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R106539 : Reach 106539 := (sr 1 106539 159809 (by norm_num) (by norm_num) (sr 2 159809 119857 (by norm_num) (by norm_num) (sr 2 119857 89893 (by norm_num) (by norm_num) (B 89893 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106543 : Reach 106543 := (sr 1 106543 159815 (by norm_num) (by norm_num) (sr 1 159815 239723 (by norm_num) (by norm_num) (sr 1 239723 359585 (by norm_num) (by norm_num) (sr 2 359585 269689 (by norm_num) (by norm_num) (sr 2 269689 202267 (by norm_num) (by norm_num) (sr 1 202267 303401 (by norm_num) (by norm_num) (sr 2 303401 227551 (by norm_num) (by norm_num) (sr 1 227551 341327 (by norm_num) (by norm_num) (sr 1 341327 511991 (by norm_num) (by norm_num) (sr 1 511991 767987 (by norm_num) (by norm_num) (sr 1 767987 1151981 (by norm_num) (by norm_num) (sr 3 1151981 431993 (by norm_num) (by norm_num) (sr 2 431993 323995 (by norm_num) (by norm_num) (sr 1 323995 485993 (by norm_num) (by norm_num) (sr 2 485993 364495 (by norm_num) (by norm_num) (sr 1 364495 546743 (by norm_num) (by norm_num) (sr 1 546743 820115 (by norm_num) (by norm_num) (sr 1 820115 1230173 (by norm_num) (by norm_num) (sr 3 1230173 461315 (by norm_num) (by norm_num) (sr 1 461315 691973 (by norm_num) (by norm_num) (sr 4 691973 129745 (by norm_num) (by norm_num) (sr 2 129745 97309 (by norm_num) (by norm_num) (B 97309 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R106547 : Reach 106547 := (sr 1 106547 159821 (by norm_num) (by norm_num) (sr 3 159821 59933 (by norm_num) (by norm_num) (B 59933 (by norm_num) (by norm_num) (by norm_num))))
theorem R106551 : Reach 106551 := (sr 1 106551 159827 (by norm_num) (by norm_num) (sr 1 159827 239741 (by norm_num) (by norm_num) (sr 3 239741 89903 (by norm_num) (by norm_num) (B 89903 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106555 : Reach 106555 := (sr 1 106555 159833 (by norm_num) (by norm_num) (sr 2 159833 119875 (by norm_num) (by norm_num) (sr 1 119875 179813 (by norm_num) (by norm_num) (sr 4 179813 33715 (by norm_num) (by norm_num) (B 33715 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106559 : Reach 106559 := (sr 1 106559 159839 (by norm_num) (by norm_num) (sr 1 159839 239759 (by norm_num) (by norm_num) (sr 1 239759 359639 (by norm_num) (by norm_num) (sr 1 359639 539459 (by norm_num) (by norm_num) (sr 1 539459 809189 (by norm_num) (by norm_num) (sr 4 809189 151723 (by norm_num) (by norm_num) (sr 1 151723 227585 (by norm_num) (by norm_num) (sr 2 227585 170689 (by norm_num) (by norm_num) (sr 2 170689 128017 (by norm_num) (by norm_num) (sr 2 128017 96013 (by norm_num) (by norm_num) (B 96013 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R106563 : Reach 106563 := (sr 1 106563 159845 (by norm_num) (by norm_num) (sr 4 159845 29971 (by norm_num) (by norm_num) (B 29971 (by norm_num) (by norm_num) (by norm_num))))
theorem R106567 : Reach 106567 := (sr 1 106567 159851 (by norm_num) (by norm_num) (sr 1 159851 239777 (by norm_num) (by norm_num) (sr 2 239777 179833 (by norm_num) (by norm_num) (sr 2 179833 134875 (by norm_num) (by norm_num) (sr 1 134875 202313 (by norm_num) (by norm_num) (sr 2 202313 151735 (by norm_num) (by norm_num) (sr 1 151735 227603 (by norm_num) (by norm_num) (sr 1 227603 341405 (by norm_num) (by norm_num) (sr 3 341405 128027 (by norm_num) (by norm_num) (sr 1 128027 192041 (by norm_num) (by norm_num) (sr 2 192041 144031 (by norm_num) (by norm_num) (sr 1 144031 216047 (by norm_num) (by norm_num) (sr 1 216047 324071 (by norm_num) (by norm_num) (sr 1 324071 486107 (by norm_num) (by norm_num) (sr 1 486107 729161 (by norm_num) (by norm_num) (sr 2 729161 546871 (by norm_num) (by norm_num) (sr 1 546871 820307 (by norm_num) (by norm_num) (sr 1 820307 1230461 (by norm_num) (by norm_num) (sr 3 1230461 461423 (by norm_num) (by norm_num) (sr 1 461423 692135 (by norm_num) (by norm_num) (sr 1 692135 1038203 (by norm_num) (by norm_num) (sr 1 1038203 1557305 (by norm_num) (by norm_num) (sr 2 1557305 1167979 (by norm_num) (by norm_num) (sr 1 1167979 1751969 (by norm_num) (by norm_num) (sr 2 1751969 1313977 (by norm_num) (by norm_num) (sr 2 1313977 985483 (by norm_num) (by norm_num) (sr 1 985483 1478225 (by norm_num) (by norm_num) (sr 2 1478225 1108669 (by norm_num) (by norm_num) (sr 3 1108669 415751 (by norm_num) (by norm_num) (sr 1 415751 623627 (by norm_num) (by norm_num) (sr 1 623627 935441 (by norm_num) (by norm_num) (sr 2 935441 701581 (by norm_num) (by norm_num) (sr 3 701581 263093 (by norm_num) (by norm_num) (sr 5 263093 24665 (by norm_num) (by norm_num) (B 24665 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))))))))
theorem R106571 : Reach 106571 := (sr 1 106571 159857 (by norm_num) (by norm_num) (sr 2 159857 119893 (by norm_num) (by norm_num) (sr 8 119893 1405 (by norm_num) (by norm_num) (B 1405 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106575 : Reach 106575 := (sr 1 106575 159863 (by norm_num) (by norm_num) (sr 1 159863 239795 (by norm_num) (by norm_num) (sr 1 239795 359693 (by norm_num) (by norm_num) (sr 3 359693 134885 (by norm_num) (by norm_num) (sr 4 134885 25291 (by norm_num) (by norm_num) (B 25291 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R106579 : Reach 106579 := (sr 1 106579 159869 (by norm_num) (by norm_num) (sr 3 159869 59951 (by norm_num) (by norm_num) (B 59951 (by norm_num) (by norm_num) (by norm_num))))
theorem R106583 : Reach 106583 := (sr 1 106583 159875 (by norm_num) (by norm_num) (sr 1 159875 239813 (by norm_num) (by norm_num) (sr 4 239813 44965 (by norm_num) (by norm_num) (B 44965 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106587 : Reach 106587 := (sr 1 106587 159881 (by norm_num) (by norm_num) (sr 2 159881 119911 (by norm_num) (by norm_num) (sr 1 119911 179867 (by norm_num) (by norm_num) (sr 1 179867 269801 (by norm_num) (by norm_num) (sr 2 269801 202351 (by norm_num) (by norm_num) (sr 1 202351 303527 (by norm_num) (by norm_num) (sr 1 303527 455291 (by norm_num) (by norm_num) (sr 1 455291 682937 (by norm_num) (by norm_num) (sr 2 682937 512203 (by norm_num) (by norm_num) (sr 1 512203 768305 (by norm_num) (by norm_num) (sr 2 768305 576229 (by norm_num) (by norm_num) (sr 4 576229 108043 (by norm_num) (by norm_num) (sr 1 108043 162065 (by norm_num) (by norm_num) (sr 2 162065 121549 (by norm_num) (by norm_num) (sr 3 121549 45581 (by norm_num) (by norm_num) (B 45581 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R106591 : Reach 106591 := (sr 1 106591 159887 (by norm_num) (by norm_num) (sr 1 159887 239831 (by norm_num) (by norm_num) (sr 1 239831 359747 (by norm_num) (by norm_num) (sr 1 359747 539621 (by norm_num) (by norm_num) (sr 4 539621 101179 (by norm_num) (by norm_num) R101179)))))
theorem R106595 : Reach 106595 := (sr 1 106595 159893 (by norm_num) (by norm_num) (sr 6 159893 7495 (by norm_num) (by norm_num) (B 7495 (by norm_num) (by norm_num) (by norm_num))))
theorem R106599 : Reach 106599 := (sr 1 106599 159899 (by norm_num) (by norm_num) (sr 1 159899 239849 (by norm_num) (by norm_num) (sr 2 239849 179887 (by norm_num) (by norm_num) (sr 1 179887 269831 (by norm_num) (by norm_num) (sr 1 269831 404747 (by norm_num) (by norm_num) (sr 1 404747 607121 (by norm_num) (by norm_num) (sr 2 607121 455341 (by norm_num) (by norm_num) (sr 3 455341 170753 (by norm_num) (by norm_num) (sr 2 170753 128065 (by norm_num) (by norm_num) (sr 2 128065 96049 (by norm_num) (by norm_num) (B 96049 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R106603 : Reach 106603 := (sr 1 106603 159905 (by norm_num) (by norm_num) (sr 2 159905 119929 (by norm_num) (by norm_num) (sr 2 119929 89947 (by norm_num) (by norm_num) (B 89947 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106607 : Reach 106607 := (sr 1 106607 159911 (by norm_num) (by norm_num) (sr 1 159911 239867 (by norm_num) (by norm_num) (sr 1 239867 359801 (by norm_num) (by norm_num) (sr 2 359801 269851 (by norm_num) (by norm_num) (sr 1 269851 404777 (by norm_num) (by norm_num) (sr 2 404777 303583 (by norm_num) (by norm_num) (sr 1 303583 455375 (by norm_num) (by norm_num) (sr 1 455375 683063 (by norm_num) (by norm_num) (sr 1 683063 1024595 (by norm_num) (by norm_num) (sr 1 1024595 1536893 (by norm_num) (by norm_num) (sr 3 1536893 576335 (by norm_num) (by norm_num) (sr 1 576335 864503 (by norm_num) (by norm_num) (sr 1 864503 1296755 (by norm_num) (by norm_num) (sr 1 1296755 1945133 (by norm_num) (by norm_num) (sr 3 1945133 729425 (by norm_num) (by norm_num) (sr 2 729425 547069 (by norm_num) (by norm_num) (sr 3 547069 205151 (by norm_num) (by norm_num) (sr 1 205151 307727 (by norm_num) (by norm_num) (sr 1 307727 461591 (by norm_num) (by norm_num) (sr 1 461591 692387 (by norm_num) (by norm_num) (sr 1 692387 1038581 (by norm_num) (by norm_num) (sr 5 1038581 97367 (by norm_num) (by norm_num) (B 97367 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R106611 : Reach 106611 := (sr 1 106611 159917 (by norm_num) (by norm_num) (sr 3 159917 59969 (by norm_num) (by norm_num) (B 59969 (by norm_num) (by norm_num) (by norm_num))))
theorem R106615 : Reach 106615 := (sr 1 106615 159923 (by norm_num) (by norm_num) (sr 1 159923 239885 (by norm_num) (by norm_num) (sr 3 239885 89957 (by norm_num) (by norm_num) (B 89957 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106619 : Reach 106619 := (sr 1 106619 159929 (by norm_num) (by norm_num) (sr 2 159929 119947 (by norm_num) (by norm_num) (sr 1 119947 179921 (by norm_num) (by norm_num) (sr 2 179921 134941 (by norm_num) (by norm_num) (sr 3 134941 50603 (by norm_num) (by norm_num) (B 50603 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R106623 : Reach 106623 := (sr 1 106623 159935 (by norm_num) (by norm_num) (sr 1 159935 239903 (by norm_num) (by norm_num) (sr 1 239903 359855 (by norm_num) (by norm_num) (sr 1 359855 539783 (by norm_num) (by norm_num) (sr 1 539783 809675 (by norm_num) (by norm_num) (sr 1 809675 1214513 (by norm_num) (by norm_num) (sr 2 1214513 910885 (by norm_num) (by norm_num) (sr 4 910885 170791 (by norm_num) (by norm_num) (sr 1 170791 256187 (by norm_num) (by norm_num) (sr 1 256187 384281 (by norm_num) (by norm_num) (sr 2 384281 288211 (by norm_num) (by norm_num) (sr 1 288211 432317 (by norm_num) (by norm_num) (sr 3 432317 162119 (by norm_num) (by norm_num) (sr 1 162119 243179 (by norm_num) (by norm_num) (sr 1 243179 364769 (by norm_num) (by norm_num) (sr 2 364769 273577 (by norm_num) (by norm_num) (sr 2 273577 205183 (by norm_num) (by norm_num) (sr 1 205183 307775 (by norm_num) (by norm_num) (sr 1 307775 461663 (by norm_num) (by norm_num) (sr 1 461663 692495 (by norm_num) (by norm_num) (sr 1 692495 1038743 (by norm_num) (by norm_num) (sr 1 1038743 1558115 (by norm_num) (by norm_num) (sr 1 1558115 2337173 (by norm_num) (by norm_num) (sr 6 2337173 109555 (by norm_num) (by norm_num) (sr 1 109555 164333 (by norm_num) (by norm_num) (sr 3 164333 61625 (by norm_num) (by norm_num) (B 61625 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))
theorem R106627 : Reach 106627 := (sr 1 106627 159941 (by norm_num) (by norm_num) (sr 4 159941 29989 (by norm_num) (by norm_num) (B 29989 (by norm_num) (by norm_num) (by norm_num))))
theorem R106631 : Reach 106631 := (sr 1 106631 159947 (by norm_num) (by norm_num) (sr 1 159947 239921 (by norm_num) (by norm_num) (sr 2 239921 179941 (by norm_num) (by norm_num) (sr 4 179941 33739 (by norm_num) (by norm_num) (B 33739 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106635 : Reach 106635 := (sr 1 106635 159953 (by norm_num) (by norm_num) (sr 2 159953 119965 (by norm_num) (by norm_num) (sr 3 119965 44987 (by norm_num) (by norm_num) (B 44987 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106639 : Reach 106639 := (sr 1 106639 159959 (by norm_num) (by norm_num) (sr 1 159959 239939 (by norm_num) (by norm_num) (sr 1 239939 359909 (by norm_num) (by norm_num) (sr 4 359909 67483 (by norm_num) (by norm_num) (B 67483 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106643 : Reach 106643 := (sr 1 106643 159965 (by norm_num) (by norm_num) (sr 3 159965 59987 (by norm_num) (by norm_num) (B 59987 (by norm_num) (by norm_num) (by norm_num))))
theorem R106647 : Reach 106647 := (sr 1 106647 159971 (by norm_num) (by norm_num) (sr 1 159971 239957 (by norm_num) (by norm_num) (sr 10 239957 703 (by norm_num) (by norm_num) (B 703 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106651 : Reach 106651 := (sr 1 106651 159977 (by norm_num) (by norm_num) (sr 2 159977 119983 (by norm_num) (by norm_num) (sr 1 119983 179975 (by norm_num) (by norm_num) (sr 1 179975 269963 (by norm_num) (by norm_num) (sr 1 269963 404945 (by norm_num) (by norm_num) (sr 2 404945 303709 (by norm_num) (by norm_num) (sr 3 303709 113891 (by norm_num) (by norm_num) (sr 1 113891 170837 (by norm_num) (by norm_num) (sr 9 170837 1001 (by norm_num) (by norm_num) (B 1001 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R106655 : Reach 106655 := (sr 1 106655 159983 (by norm_num) (by norm_num) (sr 1 159983 239975 (by norm_num) (by norm_num) (sr 1 239975 359963 (by norm_num) (by norm_num) (sr 1 359963 539945 (by norm_num) (by norm_num) (sr 2 539945 404959 (by norm_num) (by norm_num) (sr 1 404959 607439 (by norm_num) (by norm_num) (sr 1 607439 911159 (by norm_num) (by norm_num) (sr 1 911159 1366739 (by norm_num) (by norm_num) (sr 1 1366739 2050109 (by norm_num) (by norm_num) (sr 3 2050109 768791 (by norm_num) (by norm_num) (sr 1 768791 1153187 (by norm_num) (by norm_num) (sr 1 1153187 1729781 (by norm_num) (by norm_num) (sr 5 1729781 162167 (by norm_num) (by norm_num) (sr 1 162167 243251 (by norm_num) (by norm_num) (sr 1 243251 364877 (by norm_num) (by norm_num) (sr 3 364877 136829 (by norm_num) (by norm_num) (sr 3 136829 51311 (by norm_num) (by norm_num) (B 51311 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))
theorem R106659 : Reach 106659 := (sr 1 106659 159989 (by norm_num) (by norm_num) (sr 5 159989 14999 (by norm_num) (by norm_num) (B 14999 (by norm_num) (by norm_num) (by norm_num))))
theorem R106663 : Reach 106663 := (sr 1 106663 159995 (by norm_num) (by norm_num) (sr 1 159995 239993 (by norm_num) (by norm_num) (sr 2 239993 179995 (by norm_num) (by norm_num) (sr 1 179995 269993 (by norm_num) (by norm_num) (sr 2 269993 202495 (by norm_num) (by norm_num) (sr 1 202495 303743 (by norm_num) (by norm_num) (sr 1 303743 455615 (by norm_num) (by norm_num) (sr 1 455615 683423 (by norm_num) (by norm_num) (sr 1 683423 1025135 (by norm_num) (by norm_num) (sr 1 1025135 1537703 (by norm_num) (by norm_num) (sr 1 1537703 2306555 (by norm_num) (by norm_num) (sr 1 2306555 3459833 (by norm_num) (by norm_num) (sr 2 3459833 2594875 (by norm_num) (by norm_num) (sr 1 2594875 3892313 (by norm_num) (by norm_num) (sr 2 3892313 2919235 (by norm_num) (by norm_num) (sr 1 2919235 4378853 (by norm_num) (by norm_num) (sr 4 4378853 821035 (by norm_num) (by norm_num) (sr 1 821035 1231553 (by norm_num) (by norm_num) (sr 2 1231553 923665 (by norm_num) (by norm_num) (sr 2 923665 692749 (by norm_num) (by norm_num) (sr 3 692749 259781 (by norm_num) (by norm_num) (sr 4 259781 48709 (by norm_num) (by norm_num) (B 48709 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R106667 : Reach 106667 := (sr 1 106667 160001 (by norm_num) (by norm_num) (sr 2 160001 120001 (by norm_num) (by norm_num) (sr 2 120001 90001 (by norm_num) (by norm_num) (B 90001 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106671 : Reach 106671 := (sr 1 106671 160007 (by norm_num) (by norm_num) (sr 1 160007 240011 (by norm_num) (by norm_num) (sr 1 240011 360017 (by norm_num) (by norm_num) (sr 2 360017 270013 (by norm_num) (by norm_num) (sr 3 270013 101255 (by norm_num) (by norm_num) R101255)))))
theorem R106675 : Reach 106675 := (sr 1 106675 160013 (by norm_num) (by norm_num) (sr 3 160013 60005 (by norm_num) (by norm_num) (B 60005 (by norm_num) (by norm_num) (by norm_num))))
theorem R106679 : Reach 106679 := (sr 1 106679 160019 (by norm_num) (by norm_num) (sr 1 160019 240029 (by norm_num) (by norm_num) (sr 3 240029 90011 (by norm_num) (by norm_num) (B 90011 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106683 : Reach 106683 := (sr 1 106683 160025 (by norm_num) (by norm_num) (sr 2 160025 120019 (by norm_num) (by norm_num) (sr 1 120019 180029 (by norm_num) (by norm_num) (sr 3 180029 67511 (by norm_num) (by norm_num) (B 67511 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106687 : Reach 106687 := (sr 1 106687 160031 (by norm_num) (by norm_num) (sr 1 160031 240047 (by norm_num) (by norm_num) (sr 1 240047 360071 (by norm_num) (by norm_num) (sr 1 360071 540107 (by norm_num) (by norm_num) (sr 1 540107 810161 (by norm_num) (by norm_num) (sr 2 810161 607621 (by norm_num) (by norm_num) (sr 4 607621 113929 (by norm_num) (by norm_num) (sr 2 113929 85447 (by norm_num) (by norm_num) (B 85447 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R106691 : Reach 106691 := (sr 1 106691 160037 (by norm_num) (by norm_num) (sr 4 160037 30007 (by norm_num) (by norm_num) (B 30007 (by norm_num) (by norm_num) (by norm_num))))
theorem R106695 : Reach 106695 := (sr 1 106695 160043 (by norm_num) (by norm_num) (sr 1 160043 240065 (by norm_num) (by norm_num) (sr 2 240065 180049 (by norm_num) (by norm_num) (sr 2 180049 135037 (by norm_num) (by norm_num) (sr 3 135037 50639 (by norm_num) (by norm_num) (B 50639 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R106699 : Reach 106699 := (sr 1 106699 160049 (by norm_num) (by norm_num) (sr 2 160049 120037 (by norm_num) (by norm_num) (sr 4 120037 22507 (by norm_num) (by norm_num) (B 22507 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106703 : Reach 106703 := (sr 1 106703 160055 (by norm_num) (by norm_num) (sr 1 160055 240083 (by norm_num) (by norm_num) (sr 1 240083 360125 (by norm_num) (by norm_num) (sr 3 360125 135047 (by norm_num) (by norm_num) (sr 1 135047 202571 (by norm_num) (by norm_num) (sr 1 202571 303857 (by norm_num) (by norm_num) (sr 2 303857 227893 (by norm_num) (by norm_num) (sr 5 227893 21365 (by norm_num) (by norm_num) (B 21365 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R106707 : Reach 106707 := (sr 1 106707 160061 (by norm_num) (by norm_num) (sr 3 160061 60023 (by norm_num) (by norm_num) (B 60023 (by norm_num) (by norm_num) (by norm_num))))
theorem R106711 : Reach 106711 := (sr 1 106711 160067 (by norm_num) (by norm_num) (sr 1 160067 240101 (by norm_num) (by norm_num) (sr 4 240101 45019 (by norm_num) (by norm_num) (B 45019 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106715 : Reach 106715 := (sr 1 106715 160073 (by norm_num) (by norm_num) (sr 2 160073 120055 (by norm_num) (by norm_num) (sr 1 120055 180083 (by norm_num) (by norm_num) (sr 1 180083 270125 (by norm_num) (by norm_num) (sr 3 270125 101297 (by norm_num) (by norm_num) (sr 2 101297 75973 (by norm_num) (by norm_num) (B 75973 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106719 : Reach 106719 := (sr 1 106719 160079 (by norm_num) (by norm_num) (sr 1 160079 240119 (by norm_num) (by norm_num) (sr 1 240119 360179 (by norm_num) (by norm_num) (sr 1 360179 540269 (by norm_num) (by norm_num) (sr 3 540269 202601 (by norm_num) (by norm_num) (sr 2 202601 151951 (by norm_num) (by norm_num) (sr 1 151951 227927 (by norm_num) (by norm_num) (sr 1 227927 341891 (by norm_num) (by norm_num) (sr 1 341891 512837 (by norm_num) (by norm_num) (sr 4 512837 96157 (by norm_num) (by norm_num) (B 96157 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R106723 : Reach 106723 := (sr 1 106723 160085 (by norm_num) (by norm_num) (sr 10 160085 469 (by norm_num) (by norm_num) (B 469 (by norm_num) (by norm_num) (by norm_num))))
theorem R106727 : Reach 106727 := (sr 1 106727 160091 (by norm_num) (by norm_num) (sr 1 160091 240137 (by norm_num) (by norm_num) (sr 2 240137 180103 (by norm_num) (by norm_num) (sr 1 180103 270155 (by norm_num) (by norm_num) (sr 1 270155 405233 (by norm_num) (by norm_num) (sr 2 405233 303925 (by norm_num) (by norm_num) (sr 5 303925 28493 (by norm_num) (by norm_num) (B 28493 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R106731 : Reach 106731 := (sr 1 106731 160097 (by norm_num) (by norm_num) (sr 2 160097 120073 (by norm_num) (by norm_num) (sr 2 120073 90055 (by norm_num) (by norm_num) (B 90055 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106735 : Reach 106735 := (sr 1 106735 160103 (by norm_num) (by norm_num) (sr 1 160103 240155 (by norm_num) (by norm_num) (sr 1 240155 360233 (by norm_num) (by norm_num) (sr 2 360233 270175 (by norm_num) (by norm_num) (sr 1 270175 405263 (by norm_num) (by norm_num) (sr 1 405263 607895 (by norm_num) (by norm_num) (sr 1 607895 911843 (by norm_num) (by norm_num) (sr 1 911843 1367765 (by norm_num) (by norm_num) (sr 7 1367765 32057 (by norm_num) (by norm_num) (B 32057 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R106739 : Reach 106739 := (sr 1 106739 160109 (by norm_num) (by norm_num) (sr 3 160109 60041 (by norm_num) (by norm_num) (B 60041 (by norm_num) (by norm_num) (by norm_num))))
theorem R106743 : Reach 106743 := (sr 1 106743 160115 (by norm_num) (by norm_num) (sr 1 160115 240173 (by norm_num) (by norm_num) (sr 3 240173 90065 (by norm_num) (by norm_num) (B 90065 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106747 : Reach 106747 := (sr 1 106747 160121 (by norm_num) (by norm_num) (sr 2 160121 120091 (by norm_num) (by norm_num) (sr 1 120091 180137 (by norm_num) (by norm_num) (sr 2 180137 135103 (by norm_num) (by norm_num) (sr 1 135103 202655 (by norm_num) (by norm_num) (sr 1 202655 303983 (by norm_num) (by norm_num) (sr 1 303983 455975 (by norm_num) (by norm_num) (sr 1 455975 683963 (by norm_num) (by norm_num) (sr 1 683963 1025945 (by norm_num) (by norm_num) (sr 2 1025945 769459 (by norm_num) (by norm_num) (sr 1 769459 1154189 (by norm_num) (by norm_num) (sr 3 1154189 432821 (by norm_num) (by norm_num) (sr 5 432821 40577 (by norm_num) (by norm_num) (B 40577 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R106751 : Reach 106751 := (sr 1 106751 160127 (by norm_num) (by norm_num) (sr 1 160127 240191 (by norm_num) (by norm_num) (sr 1 240191 360287 (by norm_num) (by norm_num) (sr 1 360287 540431 (by norm_num) (by norm_num) (sr 1 540431 810647 (by norm_num) (by norm_num) (sr 1 810647 1215971 (by norm_num) (by norm_num) (sr 1 1215971 1823957 (by norm_num) (by norm_num) (sr 7 1823957 42749 (by norm_num) (by norm_num) (B 42749 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R106755 : Reach 106755 := (sr 1 106755 160133 (by norm_num) (by norm_num) (sr 4 160133 30025 (by norm_num) (by norm_num) (B 30025 (by norm_num) (by norm_num) (by norm_num))))
theorem R106759 : Reach 106759 := (sr 1 106759 160139 (by norm_num) (by norm_num) (sr 1 160139 240209 (by norm_num) (by norm_num) (sr 2 240209 180157 (by norm_num) (by norm_num) (sr 3 180157 67559 (by norm_num) (by norm_num) (B 67559 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106763 : Reach 106763 := (sr 1 106763 160145 (by norm_num) (by norm_num) (sr 2 160145 120109 (by norm_num) (by norm_num) (sr 3 120109 45041 (by norm_num) (by norm_num) (B 45041 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106767 : Reach 106767 := (sr 1 106767 160151 (by norm_num) (by norm_num) (sr 1 160151 240227 (by norm_num) (by norm_num) (sr 1 240227 360341 (by norm_num) (by norm_num) (sr 6 360341 16891 (by norm_num) (by norm_num) (B 16891 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106771 : Reach 106771 := (sr 1 106771 160157 (by norm_num) (by norm_num) (sr 3 160157 60059 (by norm_num) (by norm_num) (B 60059 (by norm_num) (by norm_num) (by norm_num))))
theorem R106775 : Reach 106775 := (sr 1 106775 160163 (by norm_num) (by norm_num) (sr 1 160163 240245 (by norm_num) (by norm_num) (sr 5 240245 22523 (by norm_num) (by norm_num) (B 22523 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106779 : Reach 106779 := (sr 1 106779 160169 (by norm_num) (by norm_num) (sr 2 160169 120127 (by norm_num) (by norm_num) (sr 1 120127 180191 (by norm_num) (by norm_num) (sr 1 180191 270287 (by norm_num) (by norm_num) (sr 1 270287 405431 (by norm_num) (by norm_num) (sr 1 405431 608147 (by norm_num) (by norm_num) (sr 1 608147 912221 (by norm_num) (by norm_num) (sr 3 912221 342083 (by norm_num) (by norm_num) (sr 1 342083 513125 (by norm_num) (by norm_num) (sr 4 513125 96211 (by norm_num) (by norm_num) (B 96211 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R106783 : Reach 106783 := (sr 1 106783 160175 (by norm_num) (by norm_num) (sr 1 160175 240263 (by norm_num) (by norm_num) (sr 1 240263 360395 (by norm_num) (by norm_num) (sr 1 360395 540593 (by norm_num) (by norm_num) (sr 2 540593 405445 (by norm_num) (by norm_num) (sr 4 405445 76021 (by norm_num) (by norm_num) (B 76021 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106787 : Reach 106787 := (sr 1 106787 160181 (by norm_num) (by norm_num) (sr 5 160181 15017 (by norm_num) (by norm_num) (B 15017 (by norm_num) (by norm_num) (by norm_num))))
theorem R106791 : Reach 106791 := (sr 1 106791 160187 (by norm_num) (by norm_num) (sr 1 160187 240281 (by norm_num) (by norm_num) (sr 2 240281 180211 (by norm_num) (by norm_num) (sr 1 180211 270317 (by norm_num) (by norm_num) (sr 3 270317 101369 (by norm_num) (by norm_num) (sr 2 101369 76027 (by norm_num) (by norm_num) (B 76027 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106795 : Reach 106795 := (sr 1 106795 160193 (by norm_num) (by norm_num) (sr 2 160193 120145 (by norm_num) (by norm_num) (sr 2 120145 90109 (by norm_num) (by norm_num) (B 90109 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106799 : Reach 106799 := (sr 1 106799 160199 (by norm_num) (by norm_num) (sr 1 160199 240299 (by norm_num) (by norm_num) (sr 1 240299 360449 (by norm_num) (by norm_num) (sr 2 360449 270337 (by norm_num) (by norm_num) (sr 2 270337 202753 (by norm_num) (by norm_num) (sr 2 202753 152065 (by norm_num) (by norm_num) (sr 2 152065 114049 (by norm_num) (by norm_num) (sr 2 114049 85537 (by norm_num) (by norm_num) (B 85537 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R106803 : Reach 106803 := (sr 1 106803 160205 (by norm_num) (by norm_num) (sr 3 160205 60077 (by norm_num) (by norm_num) (B 60077 (by norm_num) (by norm_num) (by norm_num))))
theorem R106807 : Reach 106807 := (sr 1 106807 160211 (by norm_num) (by norm_num) (sr 1 160211 240317 (by norm_num) (by norm_num) (sr 3 240317 90119 (by norm_num) (by norm_num) (B 90119 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106811 : Reach 106811 := (sr 1 106811 160217 (by norm_num) (by norm_num) (sr 2 160217 120163 (by norm_num) (by norm_num) (sr 1 120163 180245 (by norm_num) (by norm_num) (sr 6 180245 8449 (by norm_num) (by norm_num) (B 8449 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106815 : Reach 106815 := (sr 1 106815 160223 (by norm_num) (by norm_num) (sr 1 160223 240335 (by norm_num) (by norm_num) (sr 1 240335 360503 (by norm_num) (by norm_num) (sr 1 360503 540755 (by norm_num) (by norm_num) (sr 1 540755 811133 (by norm_num) (by norm_num) (sr 3 811133 304175 (by norm_num) (by norm_num) (sr 1 304175 456263 (by norm_num) (by norm_num) (sr 1 456263 684395 (by norm_num) (by norm_num) (sr 1 684395 1026593 (by norm_num) (by norm_num) (sr 2 1026593 769945 (by norm_num) (by norm_num) (sr 2 769945 577459 (by norm_num) (by norm_num) (sr 1 577459 866189 (by norm_num) (by norm_num) (sr 3 866189 324821 (by norm_num) (by norm_num) (sr 7 324821 7613 (by norm_num) (by norm_num) (B 7613 (by norm_num) (by norm_num) (by norm_num))))))))))))))))
theorem R106819 : Reach 106819 := (sr 1 106819 160229 (by norm_num) (by norm_num) (sr 4 160229 30043 (by norm_num) (by norm_num) (B 30043 (by norm_num) (by norm_num) (by norm_num))))
theorem R106823 : Reach 106823 := (sr 1 106823 160235 (by norm_num) (by norm_num) (sr 1 160235 240353 (by norm_num) (by norm_num) (sr 2 240353 180265 (by norm_num) (by norm_num) (sr 2 180265 135199 (by norm_num) (by norm_num) (sr 1 135199 202799 (by norm_num) (by norm_num) (sr 1 202799 304199 (by norm_num) (by norm_num) (sr 1 304199 456299 (by norm_num) (by norm_num) (sr 1 456299 684449 (by norm_num) (by norm_num) (sr 2 684449 513337 (by norm_num) (by norm_num) (sr 2 513337 385003 (by norm_num) (by norm_num) (sr 1 385003 577505 (by norm_num) (by norm_num) (sr 2 577505 433129 (by norm_num) (by norm_num) (sr 2 433129 324847 (by norm_num) (by norm_num) (sr 1 324847 487271 (by norm_num) (by norm_num) (sr 1 487271 730907 (by norm_num) (by norm_num) (sr 1 730907 1096361 (by norm_num) (by norm_num) (sr 2 1096361 822271 (by norm_num) (by norm_num) (sr 1 822271 1233407 (by norm_num) (by norm_num) (sr 1 1233407 1850111 (by norm_num) (by norm_num) (sr 1 1850111 2775167 (by norm_num) (by norm_num) (sr 1 2775167 4162751 (by norm_num) (by norm_num) (sr 1 4162751 6244127 (by norm_num) (by norm_num) (sr 1 6244127 9366191 (by norm_num) (by norm_num) (sr 1 9366191 14049287 (by norm_num) (by norm_num) (sr 1 14049287 21073931 (by norm_num) (by norm_num) (sr 1 21073931 31610897 (by norm_num) (by norm_num) (sr 2 31610897 23708173 (by norm_num) (by norm_num) (sr 3 23708173 8890565 (by norm_num) (by norm_num) (sr 4 8890565 1666981 (by norm_num) (by norm_num) (sr 4 1666981 312559 (by norm_num) (by norm_num) (sr 1 312559 468839 (by norm_num) (by norm_num) (sr 1 468839 703259 (by norm_num) (by norm_num) (sr 1 703259 1054889 (by norm_num) (by norm_num) (sr 2 1054889 791167 (by norm_num) (by norm_num) (sr 1 791167 1186751 (by norm_num) (by norm_num) (sr 1 1186751 1780127 (by norm_num) (by norm_num) (sr 1 1780127 2670191 (by norm_num) (by norm_num) (sr 1 2670191 4005287 (by norm_num) (by norm_num) (sr 1 4005287 6007931 (by norm_num) (by norm_num) (sr 1 6007931 9011897 (by norm_num) (by norm_num) (sr 2 9011897 6758923 (by norm_num) (by norm_num) (sr 1 6758923 10138385 (by norm_num) (by norm_num) (sr 2 10138385 7603789 (by norm_num) (by norm_num) (sr 3 7603789 2851421 (by norm_num) (by norm_num) (sr 3 2851421 1069283 (by norm_num) (by norm_num) (sr 1 1069283 1603925 (by norm_num) (by norm_num) (sr 10 1603925 4699 (by norm_num) (by norm_num) (B 4699 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))))))))))))))))))))
theorem R106827 : Reach 106827 := (sr 1 106827 160241 (by norm_num) (by norm_num) (sr 2 160241 120181 (by norm_num) (by norm_num) (sr 5 120181 11267 (by norm_num) (by norm_num) (B 11267 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106831 : Reach 106831 := (sr 1 106831 160247 (by norm_num) (by norm_num) (sr 1 160247 240371 (by norm_num) (by norm_num) (sr 1 240371 360557 (by norm_num) (by norm_num) (sr 3 360557 135209 (by norm_num) (by norm_num) (sr 2 135209 101407 (by norm_num) (by norm_num) R101407)))))
theorem R106835 : Reach 106835 := (sr 1 106835 160253 (by norm_num) (by norm_num) (sr 3 160253 60095 (by norm_num) (by norm_num) (B 60095 (by norm_num) (by norm_num) (by norm_num))))
theorem R106839 : Reach 106839 := (sr 1 106839 160259 (by norm_num) (by norm_num) (sr 1 160259 240389 (by norm_num) (by norm_num) (sr 4 240389 45073 (by norm_num) (by norm_num) (B 45073 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106843 : Reach 106843 := (sr 1 106843 160265 (by norm_num) (by norm_num) (sr 2 160265 120199 (by norm_num) (by norm_num) (sr 1 120199 180299 (by norm_num) (by norm_num) (sr 1 180299 270449 (by norm_num) (by norm_num) (sr 2 270449 202837 (by norm_num) (by norm_num) (sr 8 202837 2377 (by norm_num) (by norm_num) (B 2377 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106847 : Reach 106847 := (sr 1 106847 160271 (by norm_num) (by norm_num) (sr 1 160271 240407 (by norm_num) (by norm_num) (sr 1 240407 360611 (by norm_num) (by norm_num) (sr 1 360611 540917 (by norm_num) (by norm_num) (sr 5 540917 50711 (by norm_num) (by norm_num) (B 50711 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R106851 : Reach 106851 := (sr 1 106851 160277 (by norm_num) (by norm_num) (sr 6 160277 7513 (by norm_num) (by norm_num) (B 7513 (by norm_num) (by norm_num) (by norm_num))))
theorem R106855 : Reach 106855 := (sr 1 106855 160283 (by norm_num) (by norm_num) (sr 1 160283 240425 (by norm_num) (by norm_num) (sr 2 240425 180319 (by norm_num) (by norm_num) (sr 1 180319 270479 (by norm_num) (by norm_num) (sr 1 270479 405719 (by norm_num) (by norm_num) (sr 1 405719 608579 (by norm_num) (by norm_num) (sr 1 608579 912869 (by norm_num) (by norm_num) (sr 4 912869 171163 (by norm_num) (by norm_num) (sr 1 171163 256745 (by norm_num) (by norm_num) (sr 2 256745 192559 (by norm_num) (by norm_num) (sr 1 192559 288839 (by norm_num) (by norm_num) (sr 1 288839 433259 (by norm_num) (by norm_num) (sr 1 433259 649889 (by norm_num) (by norm_num) (sr 2 649889 487417 (by norm_num) (by norm_num) (sr 2 487417 365563 (by norm_num) (by norm_num) (sr 1 365563 548345 (by norm_num) (by norm_num) (sr 2 548345 411259 (by norm_num) (by norm_num) (sr 1 411259 616889 (by norm_num) (by norm_num) (sr 2 616889 462667 (by norm_num) (by norm_num) (sr 1 462667 694001 (by norm_num) (by norm_num) (sr 2 694001 520501 (by norm_num) (by norm_num) (sr 5 520501 48797 (by norm_num) (by norm_num) (B 48797 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R106859 : Reach 106859 := (sr 1 106859 160289 (by norm_num) (by norm_num) (sr 2 160289 120217 (by norm_num) (by norm_num) (sr 2 120217 90163 (by norm_num) (by norm_num) (B 90163 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106863 : Reach 106863 := (sr 1 106863 160295 (by norm_num) (by norm_num) (sr 1 160295 240443 (by norm_num) (by norm_num) (sr 1 240443 360665 (by norm_num) (by norm_num) (sr 2 360665 270499 (by norm_num) (by norm_num) (sr 1 270499 405749 (by norm_num) (by norm_num) (sr 5 405749 38039 (by norm_num) (by norm_num) (B 38039 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106867 : Reach 106867 := (sr 1 106867 160301 (by norm_num) (by norm_num) (sr 3 160301 60113 (by norm_num) (by norm_num) (B 60113 (by norm_num) (by norm_num) (by norm_num))))
theorem R106871 : Reach 106871 := (sr 1 106871 160307 (by norm_num) (by norm_num) (sr 1 160307 240461 (by norm_num) (by norm_num) (sr 3 240461 90173 (by norm_num) (by norm_num) (B 90173 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106875 : Reach 106875 := (sr 1 106875 160313 (by norm_num) (by norm_num) (sr 2 160313 120235 (by norm_num) (by norm_num) (sr 1 120235 180353 (by norm_num) (by norm_num) (sr 2 180353 135265 (by norm_num) (by norm_num) (sr 2 135265 101449 (by norm_num) (by norm_num) (sr 2 101449 76087 (by norm_num) (by norm_num) (B 76087 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106879 : Reach 106879 := (sr 1 106879 160319 (by norm_num) (by norm_num) (sr 1 160319 240479 (by norm_num) (by norm_num) (sr 1 240479 360719 (by norm_num) (by norm_num) (sr 1 360719 541079 (by norm_num) (by norm_num) (sr 1 541079 811619 (by norm_num) (by norm_num) (sr 1 811619 1217429 (by norm_num) (by norm_num) (sr 6 1217429 57067 (by norm_num) (by norm_num) (B 57067 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R106883 : Reach 106883 := (sr 1 106883 160325 (by norm_num) (by norm_num) (sr 4 160325 30061 (by norm_num) (by norm_num) (B 30061 (by norm_num) (by norm_num) (by norm_num))))
theorem R106887 : Reach 106887 := (sr 1 106887 160331 (by norm_num) (by norm_num) (sr 1 160331 240497 (by norm_num) (by norm_num) (sr 2 240497 180373 (by norm_num) (by norm_num) (sr 6 180373 8455 (by norm_num) (by norm_num) (B 8455 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106891 : Reach 106891 := (sr 1 106891 160337 (by norm_num) (by norm_num) (sr 2 160337 120253 (by norm_num) (by norm_num) (sr 3 120253 45095 (by norm_num) (by norm_num) (B 45095 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106895 : Reach 106895 := (sr 1 106895 160343 (by norm_num) (by norm_num) (sr 1 160343 240515 (by norm_num) (by norm_num) (sr 1 240515 360773 (by norm_num) (by norm_num) (sr 4 360773 67645 (by norm_num) (by norm_num) (B 67645 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106899 : Reach 106899 := (sr 1 106899 160349 (by norm_num) (by norm_num) (sr 3 160349 60131 (by norm_num) (by norm_num) (B 60131 (by norm_num) (by norm_num) (by norm_num))))
theorem R106903 : Reach 106903 := (sr 1 106903 160355 (by norm_num) (by norm_num) (sr 1 160355 240533 (by norm_num) (by norm_num) (sr 6 240533 11275 (by norm_num) (by norm_num) (B 11275 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106907 : Reach 106907 := (sr 1 106907 160361 (by norm_num) (by norm_num) (sr 2 160361 120271 (by norm_num) (by norm_num) (sr 1 120271 180407 (by norm_num) (by norm_num) (sr 1 180407 270611 (by norm_num) (by norm_num) (sr 1 270611 405917 (by norm_num) (by norm_num) (sr 3 405917 152219 (by norm_num) (by norm_num) (sr 1 152219 228329 (by norm_num) (by norm_num) (sr 2 228329 171247 (by norm_num) (by norm_num) (sr 1 171247 256871 (by norm_num) (by norm_num) (sr 1 256871 385307 (by norm_num) (by norm_num) (sr 1 385307 577961 (by norm_num) (by norm_num) (sr 2 577961 433471 (by norm_num) (by norm_num) (sr 1 433471 650207 (by norm_num) (by norm_num) (sr 1 650207 975311 (by norm_num) (by norm_num) (sr 1 975311 1462967 (by norm_num) (by norm_num) (sr 1 1462967 2194451 (by norm_num) (by norm_num) (sr 1 2194451 3291677 (by norm_num) (by norm_num) (sr 3 3291677 1234379 (by norm_num) (by norm_num) (sr 1 1234379 1851569 (by norm_num) (by norm_num) (sr 2 1851569 1388677 (by norm_num) (by norm_num) (sr 4 1388677 260377 (by norm_num) (by norm_num) (sr 2 260377 195283 (by norm_num) (by norm_num) (sr 1 195283 292925 (by norm_num) (by norm_num) (sr 3 292925 109847 (by norm_num) (by norm_num) (sr 1 109847 164771 (by norm_num) (by norm_num) (sr 1 164771 247157 (by norm_num) (by norm_num) (sr 5 247157 23171 (by norm_num) (by norm_num) (B 23171 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))
theorem R106911 : Reach 106911 := (sr 1 106911 160367 (by norm_num) (by norm_num) (sr 1 160367 240551 (by norm_num) (by norm_num) (sr 1 240551 360827 (by norm_num) (by norm_num) (sr 1 360827 541241 (by norm_num) (by norm_num) (sr 2 541241 405931 (by norm_num) (by norm_num) (sr 1 405931 608897 (by norm_num) (by norm_num) (sr 2 608897 456673 (by norm_num) (by norm_num) (sr 2 456673 342505 (by norm_num) (by norm_num) (sr 2 342505 256879 (by norm_num) (by norm_num) (sr 1 256879 385319 (by norm_num) (by norm_num) (sr 1 385319 577979 (by norm_num) (by norm_num) (sr 1 577979 866969 (by norm_num) (by norm_num) (sr 2 866969 650227 (by norm_num) (by norm_num) (sr 1 650227 975341 (by norm_num) (by norm_num) (sr 3 975341 365753 (by norm_num) (by norm_num) (sr 2 365753 274315 (by norm_num) (by norm_num) (sr 1 274315 411473 (by norm_num) (by norm_num) (sr 2 411473 308605 (by norm_num) (by norm_num) (sr 3 308605 115727 (by norm_num) (by norm_num) (sr 1 115727 173591 (by norm_num) (by norm_num) (sr 1 173591 260387 (by norm_num) (by norm_num) (sr 1 260387 390581 (by norm_num) (by norm_num) (sr 5 390581 36617 (by norm_num) (by norm_num) (B 36617 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))
theorem R106915 : Reach 106915 := (sr 1 106915 160373 (by norm_num) (by norm_num) (sr 5 160373 15035 (by norm_num) (by norm_num) (B 15035 (by norm_num) (by norm_num) (by norm_num))))
theorem R106919 : Reach 106919 := (sr 1 106919 160379 (by norm_num) (by norm_num) (sr 1 160379 240569 (by norm_num) (by norm_num) (sr 2 240569 180427 (by norm_num) (by norm_num) (sr 1 180427 270641 (by norm_num) (by norm_num) (sr 2 270641 202981 (by norm_num) (by norm_num) (sr 4 202981 38059 (by norm_num) (by norm_num) (B 38059 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106923 : Reach 106923 := (sr 1 106923 160385 (by norm_num) (by norm_num) (sr 2 160385 120289 (by norm_num) (by norm_num) (sr 2 120289 90217 (by norm_num) (by norm_num) (B 90217 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106927 : Reach 106927 := (sr 1 106927 160391 (by norm_num) (by norm_num) (sr 1 160391 240587 (by norm_num) (by norm_num) (sr 1 240587 360881 (by norm_num) (by norm_num) (sr 2 360881 270661 (by norm_num) (by norm_num) (sr 4 270661 50749 (by norm_num) (by norm_num) (B 50749 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R106931 : Reach 106931 := (sr 1 106931 160397 (by norm_num) (by norm_num) (sr 3 160397 60149 (by norm_num) (by norm_num) (B 60149 (by norm_num) (by norm_num) (by norm_num))))
theorem R106935 : Reach 106935 := (sr 1 106935 160403 (by norm_num) (by norm_num) (sr 1 160403 240605 (by norm_num) (by norm_num) (sr 3 240605 90227 (by norm_num) (by norm_num) (B 90227 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106939 : Reach 106939 := (sr 1 106939 160409 (by norm_num) (by norm_num) (sr 2 160409 120307 (by norm_num) (by norm_num) (sr 1 120307 180461 (by norm_num) (by norm_num) (sr 3 180461 67673 (by norm_num) (by norm_num) (B 67673 (by norm_num) (by norm_num) (by norm_num))))))
theorem R106943 : Reach 106943 := (sr 1 106943 160415 (by norm_num) (by norm_num) (sr 1 160415 240623 (by norm_num) (by norm_num) (sr 1 240623 360935 (by norm_num) (by norm_num) (sr 1 360935 541403 (by norm_num) (by norm_num) (sr 1 541403 812105 (by norm_num) (by norm_num) (sr 2 812105 609079 (by norm_num) (by norm_num) (sr 1 609079 913619 (by norm_num) (by norm_num) (sr 1 913619 1370429 (by norm_num) (by norm_num) (sr 3 1370429 513911 (by norm_num) (by norm_num) (sr 1 513911 770867 (by norm_num) (by norm_num) (sr 1 770867 1156301 (by norm_num) (by norm_num) (sr 3 1156301 433613 (by norm_num) (by norm_num) (sr 3 433613 162605 (by norm_num) (by norm_num) (sr 3 162605 60977 (by norm_num) (by norm_num) (B 60977 (by norm_num) (by norm_num) (by norm_num))))))))))))))))
theorem R106947 : Reach 106947 := (sr 1 106947 160421 (by norm_num) (by norm_num) (sr 4 160421 30079 (by norm_num) (by norm_num) (B 30079 (by norm_num) (by norm_num) (by norm_num))))
theorem R106951 : Reach 106951 := (sr 1 106951 160427 (by norm_num) (by norm_num) (sr 1 160427 240641 (by norm_num) (by norm_num) (sr 2 240641 180481 (by norm_num) (by norm_num) (sr 2 180481 135361 (by norm_num) (by norm_num) (sr 2 135361 101521 (by norm_num) (by norm_num) (sr 2 101521 76141 (by norm_num) (by norm_num) (B 76141 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R106955 : Reach 106955 := (sr 1 106955 160433 (by norm_num) (by norm_num) (sr 2 160433 120325 (by norm_num) (by norm_num) (sr 4 120325 22561 (by norm_num) (by norm_num) (B 22561 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106959 : Reach 106959 := (sr 1 106959 160439 (by norm_num) (by norm_num) (sr 1 160439 240659 (by norm_num) (by norm_num) (sr 1 240659 360989 (by norm_num) (by norm_num) (sr 3 360989 135371 (by norm_num) (by norm_num) (sr 1 135371 203057 (by norm_num) (by norm_num) (sr 2 203057 152293 (by norm_num) (by norm_num) (sr 4 152293 28555 (by norm_num) (by norm_num) (B 28555 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R106963 : Reach 106963 := (sr 1 106963 160445 (by norm_num) (by norm_num) (sr 3 160445 60167 (by norm_num) (by norm_num) (B 60167 (by norm_num) (by norm_num) (by norm_num))))
theorem R106967 : Reach 106967 := (sr 1 106967 160451 (by norm_num) (by norm_num) (sr 1 160451 240677 (by norm_num) (by norm_num) (sr 4 240677 45127 (by norm_num) (by norm_num) (B 45127 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106971 : Reach 106971 := (sr 1 106971 160457 (by norm_num) (by norm_num) (sr 2 160457 120343 (by norm_num) (by norm_num) (sr 1 120343 180515 (by norm_num) (by norm_num) (sr 1 180515 270773 (by norm_num) (by norm_num) (sr 5 270773 25385 (by norm_num) (by norm_num) (B 25385 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R106975 : Reach 106975 := (sr 1 106975 160463 (by norm_num) (by norm_num) (sr 1 160463 240695 (by norm_num) (by norm_num) (sr 1 240695 361043 (by norm_num) (by norm_num) (sr 1 361043 541565 (by norm_num) (by norm_num) (sr 3 541565 203087 (by norm_num) (by norm_num) (sr 1 203087 304631 (by norm_num) (by norm_num) (sr 1 304631 456947 (by norm_num) (by norm_num) (sr 1 456947 685421 (by norm_num) (by norm_num) (sr 3 685421 257033 (by norm_num) (by norm_num) (sr 2 257033 192775 (by norm_num) (by norm_num) (sr 1 192775 289163 (by norm_num) (by norm_num) (sr 1 289163 433745 (by norm_num) (by norm_num) (sr 2 433745 325309 (by norm_num) (by norm_num) (sr 3 325309 121991 (by norm_num) (by norm_num) (sr 1 121991 182987 (by norm_num) (by norm_num) (sr 1 182987 274481 (by norm_num) (by norm_num) (sr 2 274481 205861 (by norm_num) (by norm_num) (sr 4 205861 38599 (by norm_num) (by norm_num) (B 38599 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))
theorem R106979 : Reach 106979 := (sr 1 106979 160469 (by norm_num) (by norm_num) (sr 7 160469 3761 (by norm_num) (by norm_num) (B 3761 (by norm_num) (by norm_num) (by norm_num))))
theorem R106983 : Reach 106983 := (sr 1 106983 160475 (by norm_num) (by norm_num) (sr 1 160475 240713 (by norm_num) (by norm_num) (sr 2 240713 180535 (by norm_num) (by norm_num) (sr 1 180535 270803 (by norm_num) (by norm_num) (sr 1 270803 406205 (by norm_num) (by norm_num) (sr 3 406205 152327 (by norm_num) (by norm_num) (sr 1 152327 228491 (by norm_num) (by norm_num) (sr 1 228491 342737 (by norm_num) (by norm_num) (sr 2 342737 257053 (by norm_num) (by norm_num) (sr 3 257053 96395 (by norm_num) (by norm_num) (B 96395 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R106987 : Reach 106987 := (sr 1 106987 160481 (by norm_num) (by norm_num) (sr 2 160481 120361 (by norm_num) (by norm_num) (sr 2 120361 90271 (by norm_num) (by norm_num) (B 90271 (by norm_num) (by norm_num) (by norm_num)))))
theorem R106991 : Reach 106991 := (sr 1 106991 160487 (by norm_num) (by norm_num) (sr 1 160487 240731 (by norm_num) (by norm_num) (sr 1 240731 361097 (by norm_num) (by norm_num) (sr 2 361097 270823 (by norm_num) (by norm_num) (sr 1 270823 406235 (by norm_num) (by norm_num) (sr 1 406235 609353 (by norm_num) (by norm_num) (sr 2 609353 457015 (by norm_num) (by norm_num) (sr 1 457015 685523 (by norm_num) (by norm_num) (sr 1 685523 1028285 (by norm_num) (by norm_num) (sr 3 1028285 385607 (by norm_num) (by norm_num) (sr 1 385607 578411 (by norm_num) (by norm_num) (sr 1 578411 867617 (by norm_num) (by norm_num) (sr 2 867617 650713 (by norm_num) (by norm_num) (sr 2 650713 488035 (by norm_num) (by norm_num) (sr 1 488035 732053 (by norm_num) (by norm_num) (sr 6 732053 34315 (by norm_num) (by norm_num) (B 34315 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))
theorem R106995 : Reach 106995 := (sr 1 106995 160493 (by norm_num) (by norm_num) (sr 3 160493 60185 (by norm_num) (by norm_num) (B 60185 (by norm_num) (by norm_num) (by norm_num))))
theorem R106999 : Reach 106999 := (sr 1 106999 160499 (by norm_num) (by norm_num) (sr 1 160499 240749 (by norm_num) (by norm_num) (sr 3 240749 90281 (by norm_num) (by norm_num) (B 90281 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107003 : Reach 107003 := (sr 1 107003 160505 (by norm_num) (by norm_num) (sr 2 160505 120379 (by norm_num) (by norm_num) (sr 1 120379 180569 (by norm_num) (by norm_num) (sr 2 180569 135427 (by norm_num) (by norm_num) (sr 1 135427 203141 (by norm_num) (by norm_num) (sr 4 203141 38089 (by norm_num) (by norm_num) (B 38089 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107007 : Reach 107007 := (sr 1 107007 160511 (by norm_num) (by norm_num) (sr 1 160511 240767 (by norm_num) (by norm_num) (sr 1 240767 361151 (by norm_num) (by norm_num) (sr 1 361151 541727 (by norm_num) (by norm_num) (sr 1 541727 812591 (by norm_num) (by norm_num) (sr 1 812591 1218887 (by norm_num) (by norm_num) (sr 1 1218887 1828331 (by norm_num) (by norm_num) (sr 1 1828331 2742497 (by norm_num) (by norm_num) (sr 2 2742497 2056873 (by norm_num) (by norm_num) (sr 2 2056873 1542655 (by norm_num) (by norm_num) (sr 1 1542655 2313983 (by norm_num) (by norm_num) (sr 1 2313983 3470975 (by norm_num) (by norm_num) (sr 1 3470975 5206463 (by norm_num) (by norm_num) (sr 1 5206463 7809695 (by norm_num) (by norm_num) (sr 1 7809695 11714543 (by norm_num) (by norm_num) (sr 1 11714543 17571815 (by norm_num) (by norm_num) (sr 1 17571815 26357723 (by norm_num) (by norm_num) (sr 1 26357723 39536585 (by norm_num) (by norm_num) (sr 2 39536585 29652439 (by norm_num) (by norm_num) (sr 1 29652439 44478659 (by norm_num) (by norm_num) (sr 1 44478659 66717989 (by norm_num) (by norm_num) (sr 4 66717989 12509623 (by norm_num) (by norm_num) (sr 1 12509623 18764435 (by norm_num) (by norm_num) (sr 1 18764435 28146653 (by norm_num) (by norm_num) (sr 3 28146653 10554995 (by norm_num) (by norm_num) (sr 1 10554995 15832493 (by norm_num) (by norm_num) (sr 3 15832493 5937185 (by norm_num) (by norm_num) (sr 2 5937185 4452889 (by norm_num) (by norm_num) (sr 2 4452889 3339667 (by norm_num) (by norm_num) (sr 1 3339667 5009501 (by norm_num) (by norm_num) (sr 3 5009501 1878563 (by norm_num) (by norm_num) (sr 1 1878563 2817845 (by norm_num) (by norm_num) (sr 5 2817845 264173 (by norm_num) (by norm_num) (sr 3 264173 99065 (by norm_num) (by norm_num) (B 99065 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))))))))
theorem R107011 : Reach 107011 := (sr 1 107011 160517 (by norm_num) (by norm_num) (sr 4 160517 30097 (by norm_num) (by norm_num) (B 30097 (by norm_num) (by norm_num) (by norm_num))))
theorem R107015 : Reach 107015 := (sr 1 107015 160523 (by norm_num) (by norm_num) (sr 1 160523 240785 (by norm_num) (by norm_num) (sr 2 240785 180589 (by norm_num) (by norm_num) (sr 3 180589 67721 (by norm_num) (by norm_num) (B 67721 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107019 : Reach 107019 := (sr 1 107019 160529 (by norm_num) (by norm_num) (sr 2 160529 120397 (by norm_num) (by norm_num) (sr 3 120397 45149 (by norm_num) (by norm_num) (B 45149 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107023 : Reach 107023 := (sr 1 107023 160535 (by norm_num) (by norm_num) (sr 1 160535 240803 (by norm_num) (by norm_num) (sr 1 240803 361205 (by norm_num) (by norm_num) (sr 5 361205 33863 (by norm_num) (by norm_num) (B 33863 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107027 : Reach 107027 := (sr 1 107027 160541 (by norm_num) (by norm_num) (sr 3 160541 60203 (by norm_num) (by norm_num) (B 60203 (by norm_num) (by norm_num) (by norm_num))))
theorem R107031 : Reach 107031 := (sr 1 107031 160547 (by norm_num) (by norm_num) (sr 1 160547 240821 (by norm_num) (by norm_num) (sr 5 240821 22577 (by norm_num) (by norm_num) (B 22577 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107035 : Reach 107035 := (sr 1 107035 160553 (by norm_num) (by norm_num) (sr 2 160553 120415 (by norm_num) (by norm_num) (sr 1 120415 180623 (by norm_num) (by norm_num) (sr 1 180623 270935 (by norm_num) (by norm_num) (sr 1 270935 406403 (by norm_num) (by norm_num) (sr 1 406403 609605 (by norm_num) (by norm_num) (sr 4 609605 114301 (by norm_num) (by norm_num) (sr 3 114301 42863 (by norm_num) (by norm_num) (B 42863 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R107039 : Reach 107039 := (sr 1 107039 160559 (by norm_num) (by norm_num) (sr 1 160559 240839 (by norm_num) (by norm_num) (sr 1 240839 361259 (by norm_num) (by norm_num) (sr 1 361259 541889 (by norm_num) (by norm_num) (sr 2 541889 406417 (by norm_num) (by norm_num) (sr 2 406417 304813 (by norm_num) (by norm_num) (sr 3 304813 114305 (by norm_num) (by norm_num) (sr 2 114305 85729 (by norm_num) (by norm_num) (B 85729 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R107043 : Reach 107043 := (sr 1 107043 160565 (by norm_num) (by norm_num) (sr 5 160565 15053 (by norm_num) (by norm_num) (B 15053 (by norm_num) (by norm_num) (by norm_num))))
theorem R107047 : Reach 107047 := (sr 1 107047 160571 (by norm_num) (by norm_num) (sr 1 160571 240857 (by norm_num) (by norm_num) (sr 2 240857 180643 (by norm_num) (by norm_num) (sr 1 180643 270965 (by norm_num) (by norm_num) (sr 5 270965 25403 (by norm_num) (by norm_num) (B 25403 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R107051 : Reach 107051 := (sr 1 107051 160577 (by norm_num) (by norm_num) (sr 2 160577 120433 (by norm_num) (by norm_num) (sr 2 120433 90325 (by norm_num) (by norm_num) (B 90325 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107055 : Reach 107055 := (sr 1 107055 160583 (by norm_num) (by norm_num) (sr 1 160583 240875 (by norm_num) (by norm_num) (sr 1 240875 361313 (by norm_num) (by norm_num) (sr 2 361313 270985 (by norm_num) (by norm_num) (sr 2 270985 203239 (by norm_num) (by norm_num) (sr 1 203239 304859 (by norm_num) (by norm_num) (sr 1 304859 457289 (by norm_num) (by norm_num) (sr 2 457289 342967 (by norm_num) (by norm_num) (sr 1 342967 514451 (by norm_num) (by norm_num) (sr 1 514451 771677 (by norm_num) (by norm_num) (sr 3 771677 289379 (by norm_num) (by norm_num) (sr 1 289379 434069 (by norm_num) (by norm_num) (sr 6 434069 20347 (by norm_num) (by norm_num) (B 20347 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R107059 : Reach 107059 := (sr 1 107059 160589 (by norm_num) (by norm_num) (sr 3 160589 60221 (by norm_num) (by norm_num) (B 60221 (by norm_num) (by norm_num) (by norm_num))))
theorem R107063 : Reach 107063 := (sr 1 107063 160595 (by norm_num) (by norm_num) (sr 1 160595 240893 (by norm_num) (by norm_num) (sr 3 240893 90335 (by norm_num) (by norm_num) (B 90335 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107067 : Reach 107067 := (sr 1 107067 160601 (by norm_num) (by norm_num) (sr 2 160601 120451 (by norm_num) (by norm_num) (sr 1 120451 180677 (by norm_num) (by norm_num) (sr 4 180677 33877 (by norm_num) (by norm_num) (B 33877 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107071 : Reach 107071 := (sr 1 107071 160607 (by norm_num) (by norm_num) (sr 1 160607 240911 (by norm_num) (by norm_num) (sr 1 240911 361367 (by norm_num) (by norm_num) (sr 1 361367 542051 (by norm_num) (by norm_num) (sr 1 542051 813077 (by norm_num) (by norm_num) (sr 6 813077 38113 (by norm_num) (by norm_num) (B 38113 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107075 : Reach 107075 := (sr 1 107075 160613 (by norm_num) (by norm_num) (sr 4 160613 30115 (by norm_num) (by norm_num) (B 30115 (by norm_num) (by norm_num) (by norm_num))))
theorem R107079 : Reach 107079 := (sr 1 107079 160619 (by norm_num) (by norm_num) (sr 1 160619 240929 (by norm_num) (by norm_num) (sr 2 240929 180697 (by norm_num) (by norm_num) (sr 2 180697 135523 (by norm_num) (by norm_num) (sr 1 135523 203285 (by norm_num) (by norm_num) (sr 6 203285 9529 (by norm_num) (by norm_num) (B 9529 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107083 : Reach 107083 := (sr 1 107083 160625 (by norm_num) (by norm_num) (sr 2 160625 120469 (by norm_num) (by norm_num) (sr 6 120469 5647 (by norm_num) (by norm_num) (B 5647 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107087 : Reach 107087 := (sr 1 107087 160631 (by norm_num) (by norm_num) (sr 1 160631 240947 (by norm_num) (by norm_num) (sr 1 240947 361421 (by norm_num) (by norm_num) (sr 3 361421 135533 (by norm_num) (by norm_num) (sr 3 135533 50825 (by norm_num) (by norm_num) (B 50825 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R107091 : Reach 107091 := (sr 1 107091 160637 (by norm_num) (by norm_num) (sr 3 160637 60239 (by norm_num) (by norm_num) (B 60239 (by norm_num) (by norm_num) (by norm_num))))
theorem R107095 : Reach 107095 := (sr 1 107095 160643 (by norm_num) (by norm_num) (sr 1 160643 240965 (by norm_num) (by norm_num) (sr 4 240965 45181 (by norm_num) (by norm_num) (B 45181 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107099 : Reach 107099 := (sr 1 107099 160649 (by norm_num) (by norm_num) (sr 2 160649 120487 (by norm_num) (by norm_num) (sr 1 120487 180731 (by norm_num) (by norm_num) (sr 1 180731 271097 (by norm_num) (by norm_num) (sr 2 271097 203323 (by norm_num) (by norm_num) (sr 1 203323 304985 (by norm_num) (by norm_num) (sr 2 304985 228739 (by norm_num) (by norm_num) (sr 1 228739 343109 (by norm_num) (by norm_num) (sr 4 343109 64333 (by norm_num) (by norm_num) (B 64333 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R107103 : Reach 107103 := (sr 1 107103 160655 (by norm_num) (by norm_num) (sr 1 160655 240983 (by norm_num) (by norm_num) (sr 1 240983 361475 (by norm_num) (by norm_num) (sr 1 361475 542213 (by norm_num) (by norm_num) (sr 4 542213 101665 (by norm_num) (by norm_num) (sr 2 101665 76249 (by norm_num) (by norm_num) (B 76249 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107107 : Reach 107107 := (sr 1 107107 160661 (by norm_num) (by norm_num) (sr 6 160661 7531 (by norm_num) (by norm_num) (B 7531 (by norm_num) (by norm_num) (by norm_num))))
theorem R107111 : Reach 107111 := (sr 1 107111 160667 (by norm_num) (by norm_num) (sr 1 160667 241001 (by norm_num) (by norm_num) (sr 2 241001 180751 (by norm_num) (by norm_num) (sr 1 180751 271127 (by norm_num) (by norm_num) (sr 1 271127 406691 (by norm_num) (by norm_num) (sr 1 406691 610037 (by norm_num) (by norm_num) (sr 5 610037 57191 (by norm_num) (by norm_num) (B 57191 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R107115 : Reach 107115 := (sr 1 107115 160673 (by norm_num) (by norm_num) (sr 2 160673 120505 (by norm_num) (by norm_num) (sr 2 120505 90379 (by norm_num) (by norm_num) (B 90379 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107119 : Reach 107119 := (sr 1 107119 160679 (by norm_num) (by norm_num) (sr 1 160679 241019 (by norm_num) (by norm_num) (sr 1 241019 361529 (by norm_num) (by norm_num) (sr 2 361529 271147 (by norm_num) (by norm_num) (sr 1 271147 406721 (by norm_num) (by norm_num) (sr 2 406721 305041 (by norm_num) (by norm_num) (sr 2 305041 228781 (by norm_num) (by norm_num) (sr 3 228781 85793 (by norm_num) (by norm_num) (B 85793 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R107123 : Reach 107123 := (sr 1 107123 160685 (by norm_num) (by norm_num) (sr 3 160685 60257 (by norm_num) (by norm_num) (B 60257 (by norm_num) (by norm_num) (by norm_num))))
theorem R107127 : Reach 107127 := (sr 1 107127 160691 (by norm_num) (by norm_num) (sr 1 160691 241037 (by norm_num) (by norm_num) (sr 3 241037 90389 (by norm_num) (by norm_num) (B 90389 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107131 : Reach 107131 := (sr 1 107131 160697 (by norm_num) (by norm_num) (sr 2 160697 120523 (by norm_num) (by norm_num) (sr 1 120523 180785 (by norm_num) (by norm_num) (sr 2 180785 135589 (by norm_num) (by norm_num) (sr 4 135589 25423 (by norm_num) (by norm_num) (B 25423 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R107135 : Reach 107135 := (sr 1 107135 160703 (by norm_num) (by norm_num) (sr 1 160703 241055 (by norm_num) (by norm_num) (sr 1 241055 361583 (by norm_num) (by norm_num) (sr 1 361583 542375 (by norm_num) (by norm_num) (sr 1 542375 813563 (by norm_num) (by norm_num) (sr 1 813563 1220345 (by norm_num) (by norm_num) (sr 2 1220345 915259 (by norm_num) (by norm_num) (sr 1 915259 1372889 (by norm_num) (by norm_num) (sr 2 1372889 1029667 (by norm_num) (by norm_num) (sr 1 1029667 1544501 (by norm_num) (by norm_num) (sr 5 1544501 144797 (by norm_num) (by norm_num) (sr 3 144797 54299 (by norm_num) (by norm_num) (B 54299 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R107139 : Reach 107139 := (sr 1 107139 160709 (by norm_num) (by norm_num) (sr 4 160709 30133 (by norm_num) (by norm_num) (B 30133 (by norm_num) (by norm_num) (by norm_num))))
theorem R107143 : Reach 107143 := (sr 1 107143 160715 (by norm_num) (by norm_num) (sr 1 160715 241073 (by norm_num) (by norm_num) (sr 2 241073 180805 (by norm_num) (by norm_num) (sr 4 180805 33901 (by norm_num) (by norm_num) (B 33901 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107147 : Reach 107147 := (sr 1 107147 160721 (by norm_num) (by norm_num) (sr 2 160721 120541 (by norm_num) (by norm_num) (sr 3 120541 45203 (by norm_num) (by norm_num) (B 45203 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107151 : Reach 107151 := (sr 1 107151 160727 (by norm_num) (by norm_num) (sr 1 160727 241091 (by norm_num) (by norm_num) (sr 1 241091 361637 (by norm_num) (by norm_num) (sr 4 361637 67807 (by norm_num) (by norm_num) (B 67807 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107155 : Reach 107155 := (sr 1 107155 160733 (by norm_num) (by norm_num) (sr 3 160733 60275 (by norm_num) (by norm_num) (B 60275 (by norm_num) (by norm_num) (by norm_num))))
theorem R107159 : Reach 107159 := (sr 1 107159 160739 (by norm_num) (by norm_num) (sr 1 160739 241109 (by norm_num) (by norm_num) (sr 7 241109 5651 (by norm_num) (by norm_num) (B 5651 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107163 : Reach 107163 := (sr 1 107163 160745 (by norm_num) (by norm_num) (sr 2 160745 120559 (by norm_num) (by norm_num) (sr 1 120559 180839 (by norm_num) (by norm_num) (sr 1 180839 271259 (by norm_num) (by norm_num) (sr 1 271259 406889 (by norm_num) (by norm_num) (sr 2 406889 305167 (by norm_num) (by norm_num) (sr 1 305167 457751 (by norm_num) (by norm_num) (sr 1 457751 686627 (by norm_num) (by norm_num) (sr 1 686627 1029941 (by norm_num) (by norm_num) (sr 5 1029941 96557 (by norm_num) (by norm_num) (B 96557 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R107167 : Reach 107167 := (sr 1 107167 160751 (by norm_num) (by norm_num) (sr 1 160751 241127 (by norm_num) (by norm_num) (sr 1 241127 361691 (by norm_num) (by norm_num) (sr 1 361691 542537 (by norm_num) (by norm_num) (sr 2 542537 406903 (by norm_num) (by norm_num) (sr 1 406903 610355 (by norm_num) (by norm_num) (sr 1 610355 915533 (by norm_num) (by norm_num) (sr 3 915533 343325 (by norm_num) (by norm_num) (sr 3 343325 128747 (by norm_num) (by norm_num) (sr 1 128747 193121 (by norm_num) (by norm_num) (sr 2 193121 144841 (by norm_num) (by norm_num) (sr 2 144841 108631 (by norm_num) (by norm_num) (sr 1 108631 162947 (by norm_num) (by norm_num) (sr 1 162947 244421 (by norm_num) (by norm_num) (sr 4 244421 45829 (by norm_num) (by norm_num) (B 45829 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R107171 : Reach 107171 := (sr 1 107171 160757 (by norm_num) (by norm_num) (sr 5 160757 15071 (by norm_num) (by norm_num) (B 15071 (by norm_num) (by norm_num) (by norm_num))))
theorem R107175 : Reach 107175 := (sr 1 107175 160763 (by norm_num) (by norm_num) (sr 1 160763 241145 (by norm_num) (by norm_num) (sr 2 241145 180859 (by norm_num) (by norm_num) (sr 1 180859 271289 (by norm_num) (by norm_num) (sr 2 271289 203467 (by norm_num) (by norm_num) (sr 1 203467 305201 (by norm_num) (by norm_num) (sr 2 305201 228901 (by norm_num) (by norm_num) (sr 4 228901 42919 (by norm_num) (by norm_num) (B 42919 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R107179 : Reach 107179 := (sr 1 107179 160769 (by norm_num) (by norm_num) (sr 2 160769 120577 (by norm_num) (by norm_num) (sr 2 120577 90433 (by norm_num) (by norm_num) (B 90433 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107183 : Reach 107183 := (sr 1 107183 160775 (by norm_num) (by norm_num) (sr 1 160775 241163 (by norm_num) (by norm_num) (sr 1 241163 361745 (by norm_num) (by norm_num) (sr 2 361745 271309 (by norm_num) (by norm_num) (sr 3 271309 101741 (by norm_num) (by norm_num) (sr 3 101741 38153 (by norm_num) (by norm_num) (B 38153 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107187 : Reach 107187 := (sr 1 107187 160781 (by norm_num) (by norm_num) (sr 3 160781 60293 (by norm_num) (by norm_num) (B 60293 (by norm_num) (by norm_num) (by norm_num))))
theorem R107191 : Reach 107191 := (sr 1 107191 160787 (by norm_num) (by norm_num) (sr 1 160787 241181 (by norm_num) (by norm_num) (sr 3 241181 90443 (by norm_num) (by norm_num) (B 90443 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107195 : Reach 107195 := (sr 1 107195 160793 (by norm_num) (by norm_num) (sr 2 160793 120595 (by norm_num) (by norm_num) (sr 1 120595 180893 (by norm_num) (by norm_num) (sr 3 180893 67835 (by norm_num) (by norm_num) (B 67835 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107199 : Reach 107199 := (sr 1 107199 160799 (by norm_num) (by norm_num) (sr 1 160799 241199 (by norm_num) (by norm_num) (sr 1 241199 361799 (by norm_num) (by norm_num) (sr 1 361799 542699 (by norm_num) (by norm_num) (sr 1 542699 814049 (by norm_num) (by norm_num) (sr 2 814049 610537 (by norm_num) (by norm_num) (sr 2 610537 457903 (by norm_num) (by norm_num) (sr 1 457903 686855 (by norm_num) (by norm_num) (sr 1 686855 1030283 (by norm_num) (by norm_num) (sr 1 1030283 1545425 (by norm_num) (by norm_num) (sr 2 1545425 1159069 (by norm_num) (by norm_num) (sr 3 1159069 434651 (by norm_num) (by norm_num) (sr 1 434651 651977 (by norm_num) (by norm_num) (sr 2 651977 488983 (by norm_num) (by norm_num) (sr 1 488983 733475 (by norm_num) (by norm_num) (sr 1 733475 1100213 (by norm_num) (by norm_num) (sr 5 1100213 103145 (by norm_num) (by norm_num) (sr 2 103145 77359 (by norm_num) (by norm_num) (B 77359 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))
theorem R107203 : Reach 107203 := (sr 1 107203 160805 (by norm_num) (by norm_num) (sr 4 160805 30151 (by norm_num) (by norm_num) (B 30151 (by norm_num) (by norm_num) (by norm_num))))
theorem R107207 : Reach 107207 := (sr 1 107207 160811 (by norm_num) (by norm_num) (sr 1 160811 241217 (by norm_num) (by norm_num) (sr 2 241217 180913 (by norm_num) (by norm_num) (sr 2 180913 135685 (by norm_num) (by norm_num) (sr 4 135685 25441 (by norm_num) (by norm_num) (B 25441 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R107211 : Reach 107211 := (sr 1 107211 160817 (by norm_num) (by norm_num) (sr 2 160817 120613 (by norm_num) (by norm_num) (sr 4 120613 22615 (by norm_num) (by norm_num) (B 22615 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107215 : Reach 107215 := (sr 1 107215 160823 (by norm_num) (by norm_num) (sr 1 160823 241235 (by norm_num) (by norm_num) (sr 1 241235 361853 (by norm_num) (by norm_num) (sr 3 361853 135695 (by norm_num) (by norm_num) (sr 1 135695 203543 (by norm_num) (by norm_num) (sr 1 203543 305315 (by norm_num) (by norm_num) (sr 1 305315 457973 (by norm_num) (by norm_num) (sr 5 457973 42935 (by norm_num) (by norm_num) (B 42935 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R107219 : Reach 107219 := (sr 1 107219 160829 (by norm_num) (by norm_num) (sr 3 160829 60311 (by norm_num) (by norm_num) (B 60311 (by norm_num) (by norm_num) (by norm_num))))
theorem R107223 : Reach 107223 := (sr 1 107223 160835 (by norm_num) (by norm_num) (sr 1 160835 241253 (by norm_num) (by norm_num) (sr 4 241253 45235 (by norm_num) (by norm_num) (B 45235 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107227 : Reach 107227 := (sr 1 107227 160841 (by norm_num) (by norm_num) (sr 2 160841 120631 (by norm_num) (by norm_num) (sr 1 120631 180947 (by norm_num) (by norm_num) (sr 1 180947 271421 (by norm_num) (by norm_num) (sr 3 271421 101783 (by norm_num) (by norm_num) R101783)))))
theorem R107231 : Reach 107231 := (sr 1 107231 160847 (by norm_num) (by norm_num) (sr 1 160847 241271 (by norm_num) (by norm_num) (sr 1 241271 361907 (by norm_num) (by norm_num) (sr 1 361907 542861 (by norm_num) (by norm_num) (sr 3 542861 203573 (by norm_num) (by norm_num) (sr 5 203573 19085 (by norm_num) (by norm_num) (B 19085 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107235 : Reach 107235 := (sr 1 107235 160853 (by norm_num) (by norm_num) (sr 8 160853 1885 (by norm_num) (by norm_num) (B 1885 (by norm_num) (by norm_num) (by norm_num))))
theorem R107239 : Reach 107239 := (sr 1 107239 160859 (by norm_num) (by norm_num) (sr 1 160859 241289 (by norm_num) (by norm_num) (sr 2 241289 180967 (by norm_num) (by norm_num) (sr 1 180967 271451 (by norm_num) (by norm_num) (sr 1 271451 407177 (by norm_num) (by norm_num) (sr 2 407177 305383 (by norm_num) (by norm_num) (sr 1 305383 458075 (by norm_num) (by norm_num) (sr 1 458075 687113 (by norm_num) (by norm_num) (sr 2 687113 515335 (by norm_num) (by norm_num) (sr 1 515335 773003 (by norm_num) (by norm_num) (sr 1 773003 1159505 (by norm_num) (by norm_num) (sr 2 1159505 869629 (by norm_num) (by norm_num) (sr 3 869629 326111 (by norm_num) (by norm_num) (sr 1 326111 489167 (by norm_num) (by norm_num) (sr 1 489167 733751 (by norm_num) (by norm_num) (sr 1 733751 1100627 (by norm_num) (by norm_num) (sr 1 1100627 1650941 (by norm_num) (by norm_num) (sr 3 1650941 619103 (by norm_num) (by norm_num) (sr 1 619103 928655 (by norm_num) (by norm_num) (sr 1 928655 1392983 (by norm_num) (by norm_num) (sr 1 1392983 2089475 (by norm_num) (by norm_num) (sr 1 2089475 3134213 (by norm_num) (by norm_num) (sr 4 3134213 587665 (by norm_num) (by norm_num) (sr 2 587665 440749 (by norm_num) (by norm_num) (sr 3 440749 165281 (by norm_num) (by norm_num) (sr 2 165281 123961 (by norm_num) (by norm_num) (sr 2 123961 92971 (by norm_num) (by norm_num) (B 92971 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))
theorem R107243 : Reach 107243 := (sr 1 107243 160865 (by norm_num) (by norm_num) (sr 2 160865 120649 (by norm_num) (by norm_num) (sr 2 120649 90487 (by norm_num) (by norm_num) (B 90487 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107247 : Reach 107247 := (sr 1 107247 160871 (by norm_num) (by norm_num) (sr 1 160871 241307 (by norm_num) (by norm_num) (sr 1 241307 361961 (by norm_num) (by norm_num) (sr 2 361961 271471 (by norm_num) (by norm_num) (sr 1 271471 407207 (by norm_num) (by norm_num) (sr 1 407207 610811 (by norm_num) (by norm_num) (sr 1 610811 916217 (by norm_num) (by norm_num) (sr 2 916217 687163 (by norm_num) (by norm_num) (sr 1 687163 1030745 (by norm_num) (by norm_num) (sr 2 1030745 773059 (by norm_num) (by norm_num) (sr 1 773059 1159589 (by norm_num) (by norm_num) (sr 4 1159589 217423 (by norm_num) (by norm_num) (sr 1 217423 326135 (by norm_num) (by norm_num) (sr 1 326135 489203 (by norm_num) (by norm_num) (sr 1 489203 733805 (by norm_num) (by norm_num) (sr 3 733805 275177 (by norm_num) (by norm_num) (sr 2 275177 206383 (by norm_num) (by norm_num) (sr 1 206383 309575 (by norm_num) (by norm_num) (sr 1 309575 464363 (by norm_num) (by norm_num) (sr 1 464363 696545 (by norm_num) (by norm_num) (sr 2 696545 522409 (by norm_num) (by norm_num) (sr 2 522409 391807 (by norm_num) (by norm_num) (sr 1 391807 587711 (by norm_num) (by norm_num) (sr 1 587711 881567 (by norm_num) (by norm_num) (sr 1 881567 1322351 (by norm_num) (by norm_num) (sr 1 1322351 1983527 (by norm_num) (by norm_num) (sr 1 1983527 2975291 (by norm_num) (by norm_num) (sr 1 2975291 4462937 (by norm_num) (by norm_num) (sr 2 4462937 3347203 (by norm_num) (by norm_num) (sr 1 3347203 5020805 (by norm_num) (by norm_num) (sr 4 5020805 941401 (by norm_num) (by norm_num) (sr 2 941401 706051 (by norm_num) (by norm_num) (sr 1 706051 1059077 (by norm_num) (by norm_num) (sr 4 1059077 198577 (by norm_num) (by norm_num) (sr 2 198577 148933 (by norm_num) (by norm_num) (sr 4 148933 27925 (by norm_num) (by norm_num) (B 27925 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))))))))))
theorem R107251 : Reach 107251 := (sr 1 107251 160877 (by norm_num) (by norm_num) (sr 3 160877 60329 (by norm_num) (by norm_num) (B 60329 (by norm_num) (by norm_num) (by norm_num))))
theorem R107255 : Reach 107255 := (sr 1 107255 160883 (by norm_num) (by norm_num) (sr 1 160883 241325 (by norm_num) (by norm_num) (sr 3 241325 90497 (by norm_num) (by norm_num) (B 90497 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107259 : Reach 107259 := (sr 1 107259 160889 (by norm_num) (by norm_num) (sr 2 160889 120667 (by norm_num) (by norm_num) (sr 1 120667 181001 (by norm_num) (by norm_num) (sr 2 181001 135751 (by norm_num) (by norm_num) (sr 1 135751 203627 (by norm_num) (by norm_num) (sr 1 203627 305441 (by norm_num) (by norm_num) (sr 2 305441 229081 (by norm_num) (by norm_num) (sr 2 229081 171811 (by norm_num) (by norm_num) (sr 1 171811 257717 (by norm_num) (by norm_num) (sr 5 257717 24161 (by norm_num) (by norm_num) (B 24161 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R107263 : Reach 107263 := (sr 1 107263 160895 (by norm_num) (by norm_num) (sr 1 160895 241343 (by norm_num) (by norm_num) (sr 1 241343 362015 (by norm_num) (by norm_num) (sr 1 362015 543023 (by norm_num) (by norm_num) (sr 1 543023 814535 (by norm_num) (by norm_num) (sr 1 814535 1221803 (by norm_num) (by norm_num) (sr 1 1221803 1832705 (by norm_num) (by norm_num) (sr 2 1832705 1374529 (by norm_num) (by norm_num) (sr 2 1374529 1030897 (by norm_num) (by norm_num) (sr 2 1030897 773173 (by norm_num) (by norm_num) (sr 5 773173 72485 (by norm_num) (by norm_num) (B 72485 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R107267 : Reach 107267 := (sr 1 107267 160901 (by norm_num) (by norm_num) (sr 4 160901 30169 (by norm_num) (by norm_num) (B 30169 (by norm_num) (by norm_num) (by norm_num))))
theorem R107271 : Reach 107271 := (sr 1 107271 160907 (by norm_num) (by norm_num) (sr 1 160907 241361 (by norm_num) (by norm_num) (sr 2 241361 181021 (by norm_num) (by norm_num) (sr 3 181021 67883 (by norm_num) (by norm_num) (B 67883 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107275 : Reach 107275 := (sr 1 107275 160913 (by norm_num) (by norm_num) (sr 2 160913 120685 (by norm_num) (by norm_num) (sr 3 120685 45257 (by norm_num) (by norm_num) (B 45257 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107279 : Reach 107279 := (sr 1 107279 160919 (by norm_num) (by norm_num) (sr 1 160919 241379 (by norm_num) (by norm_num) (sr 1 241379 362069 (by norm_num) (by norm_num) (sr 8 362069 4243 (by norm_num) (by norm_num) (B 4243 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107283 : Reach 107283 := (sr 1 107283 160925 (by norm_num) (by norm_num) (sr 3 160925 60347 (by norm_num) (by norm_num) (B 60347 (by norm_num) (by norm_num) (by norm_num))))
theorem R107287 : Reach 107287 := (sr 1 107287 160931 (by norm_num) (by norm_num) (sr 1 160931 241397 (by norm_num) (by norm_num) (sr 5 241397 22631 (by norm_num) (by norm_num) (B 22631 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107291 : Reach 107291 := (sr 1 107291 160937 (by norm_num) (by norm_num) (sr 2 160937 120703 (by norm_num) (by norm_num) (sr 1 120703 181055 (by norm_num) (by norm_num) (sr 1 181055 271583 (by norm_num) (by norm_num) (sr 1 271583 407375 (by norm_num) (by norm_num) (sr 1 407375 611063 (by norm_num) (by norm_num) (sr 1 611063 916595 (by norm_num) (by norm_num) (sr 1 916595 1374893 (by norm_num) (by norm_num) (sr 3 1374893 515585 (by norm_num) (by norm_num) (sr 2 515585 386689 (by norm_num) (by norm_num) (sr 2 386689 290017 (by norm_num) (by norm_num) (sr 2 290017 217513 (by norm_num) (by norm_num) (sr 2 217513 163135 (by norm_num) (by norm_num) (sr 1 163135 244703 (by norm_num) (by norm_num) (sr 1 244703 367055 (by norm_num) (by norm_num) (sr 1 367055 550583 (by norm_num) (by norm_num) (sr 1 550583 825875 (by norm_num) (by norm_num) (sr 1 825875 1238813 (by norm_num) (by norm_num) (sr 3 1238813 464555 (by norm_num) (by norm_num) (sr 1 464555 696833 (by norm_num) (by norm_num) (sr 2 696833 522625 (by norm_num) (by norm_num) (sr 2 522625 391969 (by norm_num) (by norm_num) (sr 2 391969 293977 (by norm_num) (by norm_num) (sr 2 293977 220483 (by norm_num) (by norm_num) (sr 1 220483 330725 (by norm_num) (by norm_num) (sr 4 330725 62011 (by norm_num) (by norm_num) (B 62011 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))
theorem R107295 : Reach 107295 := (sr 1 107295 160943 (by norm_num) (by norm_num) (sr 1 160943 241415 (by norm_num) (by norm_num) (sr 1 241415 362123 (by norm_num) (by norm_num) (sr 1 362123 543185 (by norm_num) (by norm_num) (sr 2 543185 407389 (by norm_num) (by norm_num) (sr 3 407389 152771 (by norm_num) (by norm_num) (sr 1 152771 229157 (by norm_num) (by norm_num) (sr 4 229157 42967 (by norm_num) (by norm_num) (B 42967 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R107299 : Reach 107299 := (sr 1 107299 160949 (by norm_num) (by norm_num) (sr 5 160949 15089 (by norm_num) (by norm_num) (B 15089 (by norm_num) (by norm_num) (by norm_num))))
theorem R107303 : Reach 107303 := (sr 1 107303 160955 (by norm_num) (by norm_num) (sr 1 160955 241433 (by norm_num) (by norm_num) (sr 2 241433 181075 (by norm_num) (by norm_num) (sr 1 181075 271613 (by norm_num) (by norm_num) (sr 3 271613 101855 (by norm_num) (by norm_num) R101855)))))
theorem R107307 : Reach 107307 := (sr 1 107307 160961 (by norm_num) (by norm_num) (sr 2 160961 120721 (by norm_num) (by norm_num) (sr 2 120721 90541 (by norm_num) (by norm_num) (B 90541 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107311 : Reach 107311 := (sr 1 107311 160967 (by norm_num) (by norm_num) (sr 1 160967 241451 (by norm_num) (by norm_num) (sr 1 241451 362177 (by norm_num) (by norm_num) (sr 2 362177 271633 (by norm_num) (by norm_num) (sr 2 271633 203725 (by norm_num) (by norm_num) (sr 3 203725 76397 (by norm_num) (by norm_num) (B 76397 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107315 : Reach 107315 := (sr 1 107315 160973 (by norm_num) (by norm_num) (sr 3 160973 60365 (by norm_num) (by norm_num) (B 60365 (by norm_num) (by norm_num) (by norm_num))))
theorem R107319 : Reach 107319 := (sr 1 107319 160979 (by norm_num) (by norm_num) (sr 1 160979 241469 (by norm_num) (by norm_num) (sr 3 241469 90551 (by norm_num) (by norm_num) (B 90551 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107323 : Reach 107323 := (sr 1 107323 160985 (by norm_num) (by norm_num) (sr 2 160985 120739 (by norm_num) (by norm_num) (sr 1 120739 181109 (by norm_num) (by norm_num) (sr 5 181109 16979 (by norm_num) (by norm_num) (B 16979 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107327 : Reach 107327 := (sr 1 107327 160991 (by norm_num) (by norm_num) (sr 1 160991 241487 (by norm_num) (by norm_num) (sr 1 241487 362231 (by norm_num) (by norm_num) (sr 1 362231 543347 (by norm_num) (by norm_num) (sr 1 543347 815021 (by norm_num) (by norm_num) (sr 3 815021 305633 (by norm_num) (by norm_num) (sr 2 305633 229225 (by norm_num) (by norm_num) (sr 2 229225 171919 (by norm_num) (by norm_num) (sr 1 171919 257879 (by norm_num) (by norm_num) (sr 1 257879 386819 (by norm_num) (by norm_num) (sr 1 386819 580229 (by norm_num) (by norm_num) (sr 4 580229 108793 (by norm_num) (by norm_num) (sr 2 108793 81595 (by norm_num) (by norm_num) (B 81595 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R107331 : Reach 107331 := (sr 1 107331 160997 (by norm_num) (by norm_num) (sr 4 160997 30187 (by norm_num) (by norm_num) (B 30187 (by norm_num) (by norm_num) (by norm_num))))
theorem R107335 : Reach 107335 := (sr 1 107335 161003 (by norm_num) (by norm_num) (sr 1 161003 241505 (by norm_num) (by norm_num) (sr 2 241505 181129 (by norm_num) (by norm_num) (sr 2 181129 135847 (by norm_num) (by norm_num) (sr 1 135847 203771 (by norm_num) (by norm_num) (sr 1 203771 305657 (by norm_num) (by norm_num) (sr 2 305657 229243 (by norm_num) (by norm_num) (sr 1 229243 343865 (by norm_num) (by norm_num) (sr 2 343865 257899 (by norm_num) (by norm_num) (sr 1 257899 386849 (by norm_num) (by norm_num) (sr 2 386849 290137 (by norm_num) (by norm_num) (sr 2 290137 217603 (by norm_num) (by norm_num) (sr 1 217603 326405 (by norm_num) (by norm_num) (sr 4 326405 61201 (by norm_num) (by norm_num) (B 61201 (by norm_num) (by norm_num) (by norm_num))))))))))))))))
theorem R107339 : Reach 107339 := (sr 1 107339 161009 (by norm_num) (by norm_num) (sr 2 161009 120757 (by norm_num) (by norm_num) (sr 5 120757 11321 (by norm_num) (by norm_num) (B 11321 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107343 : Reach 107343 := (sr 1 107343 161015 (by norm_num) (by norm_num) (sr 1 161015 241523 (by norm_num) (by norm_num) (sr 1 241523 362285 (by norm_num) (by norm_num) (sr 3 362285 135857 (by norm_num) (by norm_num) (sr 2 135857 101893 (by norm_num) (by norm_num) (sr 4 101893 19105 (by norm_num) (by norm_num) (B 19105 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107347 : Reach 107347 := (sr 1 107347 161021 (by norm_num) (by norm_num) (sr 3 161021 60383 (by norm_num) (by norm_num) (B 60383 (by norm_num) (by norm_num) (by norm_num))))
theorem R107351 : Reach 107351 := (sr 1 107351 161027 (by norm_num) (by norm_num) (sr 1 161027 241541 (by norm_num) (by norm_num) (sr 4 241541 45289 (by norm_num) (by norm_num) (B 45289 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107355 : Reach 107355 := (sr 1 107355 161033 (by norm_num) (by norm_num) (sr 2 161033 120775 (by norm_num) (by norm_num) (sr 1 120775 181163 (by norm_num) (by norm_num) (sr 1 181163 271745 (by norm_num) (by norm_num) (sr 2 271745 203809 (by norm_num) (by norm_num) (sr 2 203809 152857 (by norm_num) (by norm_num) (sr 2 152857 114643 (by norm_num) (by norm_num) (sr 1 114643 171965 (by norm_num) (by norm_num) (sr 3 171965 64487 (by norm_num) (by norm_num) (B 64487 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R107359 : Reach 107359 := (sr 1 107359 161039 (by norm_num) (by norm_num) (sr 1 161039 241559 (by norm_num) (by norm_num) (sr 1 241559 362339 (by norm_num) (by norm_num) (sr 1 362339 543509 (by norm_num) (by norm_num) (sr 6 543509 25477 (by norm_num) (by norm_num) (B 25477 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R107363 : Reach 107363 := (sr 1 107363 161045 (by norm_num) (by norm_num) (sr 6 161045 7549 (by norm_num) (by norm_num) (B 7549 (by norm_num) (by norm_num) (by norm_num))))
theorem R107367 : Reach 107367 := (sr 1 107367 161051 (by norm_num) (by norm_num) (sr 1 161051 241577 (by norm_num) (by norm_num) (sr 2 241577 181183 (by norm_num) (by norm_num) (sr 1 181183 271775 (by norm_num) (by norm_num) (sr 1 271775 407663 (by norm_num) (by norm_num) (sr 1 407663 611495 (by norm_num) (by norm_num) (sr 1 611495 917243 (by norm_num) (by norm_num) (sr 1 917243 1375865 (by norm_num) (by norm_num) (sr 2 1375865 1031899 (by norm_num) (by norm_num) (sr 1 1031899 1547849 (by norm_num) (by norm_num) (sr 2 1547849 1160887 (by norm_num) (by norm_num) (sr 1 1160887 1741331 (by norm_num) (by norm_num) (sr 1 1741331 2611997 (by norm_num) (by norm_num) (sr 3 2611997 979499 (by norm_num) (by norm_num) (sr 1 979499 1469249 (by norm_num) (by norm_num) (sr 2 1469249 1101937 (by norm_num) (by norm_num) (sr 2 1101937 826453 (by norm_num) (by norm_num) (sr 8 826453 9685 (by norm_num) (by norm_num) (B 9685 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))
theorem R107371 : Reach 107371 := (sr 1 107371 161057 (by norm_num) (by norm_num) (sr 2 161057 120793 (by norm_num) (by norm_num) (sr 2 120793 90595 (by norm_num) (by norm_num) (B 90595 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107375 : Reach 107375 := (sr 1 107375 161063 (by norm_num) (by norm_num) (sr 1 161063 241595 (by norm_num) (by norm_num) (sr 1 241595 362393 (by norm_num) (by norm_num) (sr 2 362393 271795 (by norm_num) (by norm_num) (sr 1 271795 407693 (by norm_num) (by norm_num) (sr 3 407693 152885 (by norm_num) (by norm_num) (sr 5 152885 14333 (by norm_num) (by norm_num) (B 14333 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R107379 : Reach 107379 := (sr 1 107379 161069 (by norm_num) (by norm_num) (sr 3 161069 60401 (by norm_num) (by norm_num) (B 60401 (by norm_num) (by norm_num) (by norm_num))))
theorem R107383 : Reach 107383 := (sr 1 107383 161075 (by norm_num) (by norm_num) (sr 1 161075 241613 (by norm_num) (by norm_num) (sr 3 241613 90605 (by norm_num) (by norm_num) (B 90605 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107387 : Reach 107387 := (sr 1 107387 161081 (by norm_num) (by norm_num) (sr 2 161081 120811 (by norm_num) (by norm_num) (sr 1 120811 181217 (by norm_num) (by norm_num) (sr 2 181217 135913 (by norm_num) (by norm_num) (sr 2 135913 101935 (by norm_num) (by norm_num) R101935)))))
theorem R107391 : Reach 107391 := (sr 1 107391 161087 (by norm_num) (by norm_num) (sr 1 161087 241631 (by norm_num) (by norm_num) (sr 1 241631 362447 (by norm_num) (by norm_num) (sr 1 362447 543671 (by norm_num) (by norm_num) (sr 1 543671 815507 (by norm_num) (by norm_num) (sr 1 815507 1223261 (by norm_num) (by norm_num) (sr 3 1223261 458723 (by norm_num) (by norm_num) (sr 1 458723 688085 (by norm_num) (by norm_num) (sr 7 688085 16127 (by norm_num) (by norm_num) (B 16127 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R107395 : Reach 107395 := (sr 1 107395 161093 (by norm_num) (by norm_num) (sr 4 161093 30205 (by norm_num) (by norm_num) (B 30205 (by norm_num) (by norm_num) (by norm_num))))
theorem R107399 : Reach 107399 := (sr 1 107399 161099 (by norm_num) (by norm_num) (sr 1 161099 241649 (by norm_num) (by norm_num) (sr 2 241649 181237 (by norm_num) (by norm_num) (sr 5 181237 16991 (by norm_num) (by norm_num) (B 16991 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107403 : Reach 107403 := (sr 1 107403 161105 (by norm_num) (by norm_num) (sr 2 161105 120829 (by norm_num) (by norm_num) (sr 3 120829 45311 (by norm_num) (by norm_num) (B 45311 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107407 : Reach 107407 := (sr 1 107407 161111 (by norm_num) (by norm_num) (sr 1 161111 241667 (by norm_num) (by norm_num) (sr 1 241667 362501 (by norm_num) (by norm_num) (sr 4 362501 67969 (by norm_num) (by norm_num) (B 67969 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107411 : Reach 107411 := (sr 1 107411 161117 (by norm_num) (by norm_num) (sr 3 161117 60419 (by norm_num) (by norm_num) (B 60419 (by norm_num) (by norm_num) (by norm_num))))
theorem R107415 : Reach 107415 := (sr 1 107415 161123 (by norm_num) (by norm_num) (sr 1 161123 241685 (by norm_num) (by norm_num) (sr 6 241685 11329 (by norm_num) (by norm_num) (B 11329 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107419 : Reach 107419 := (sr 1 107419 161129 (by norm_num) (by norm_num) (sr 2 161129 120847 (by norm_num) (by norm_num) (sr 1 120847 181271 (by norm_num) (by norm_num) (sr 1 181271 271907 (by norm_num) (by norm_num) (sr 1 271907 407861 (by norm_num) (by norm_num) (sr 5 407861 38237 (by norm_num) (by norm_num) (B 38237 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107423 : Reach 107423 := (sr 1 107423 161135 (by norm_num) (by norm_num) (sr 1 161135 241703 (by norm_num) (by norm_num) (sr 1 241703 362555 (by norm_num) (by norm_num) (sr 1 362555 543833 (by norm_num) (by norm_num) (sr 2 543833 407875 (by norm_num) (by norm_num) (sr 1 407875 611813 (by norm_num) (by norm_num) (sr 4 611813 114715 (by norm_num) (by norm_num) (sr 1 114715 172073 (by norm_num) (by norm_num) (sr 2 172073 129055 (by norm_num) (by norm_num) (sr 1 129055 193583 (by norm_num) (by norm_num) (sr 1 193583 290375 (by norm_num) (by norm_num) (sr 1 290375 435563 (by norm_num) (by norm_num) (sr 1 435563 653345 (by norm_num) (by norm_num) (sr 2 653345 490009 (by norm_num) (by norm_num) (sr 2 490009 367507 (by norm_num) (by norm_num) (sr 1 367507 551261 (by norm_num) (by norm_num) (sr 3 551261 206723 (by norm_num) (by norm_num) (sr 1 206723 310085 (by norm_num) (by norm_num) (sr 4 310085 58141 (by norm_num) (by norm_num) (B 58141 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))
theorem R107427 : Reach 107427 := (sr 1 107427 161141 (by norm_num) (by norm_num) (sr 5 161141 15107 (by norm_num) (by norm_num) (B 15107 (by norm_num) (by norm_num) (by norm_num))))
theorem R107431 : Reach 107431 := (sr 1 107431 161147 (by norm_num) (by norm_num) (sr 1 161147 241721 (by norm_num) (by norm_num) (sr 2 241721 181291 (by norm_num) (by norm_num) (sr 1 181291 271937 (by norm_num) (by norm_num) (sr 2 271937 203953 (by norm_num) (by norm_num) (sr 2 203953 152965 (by norm_num) (by norm_num) (sr 4 152965 28681 (by norm_num) (by norm_num) (B 28681 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R107435 : Reach 107435 := (sr 1 107435 161153 (by norm_num) (by norm_num) (sr 2 161153 120865 (by norm_num) (by norm_num) (sr 2 120865 90649 (by norm_num) (by norm_num) (B 90649 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107439 : Reach 107439 := (sr 1 107439 161159 (by norm_num) (by norm_num) (sr 1 161159 241739 (by norm_num) (by norm_num) (sr 1 241739 362609 (by norm_num) (by norm_num) (sr 2 362609 271957 (by norm_num) (by norm_num) (sr 8 271957 3187 (by norm_num) (by norm_num) (B 3187 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R107443 : Reach 107443 := (sr 1 107443 161165 (by norm_num) (by norm_num) (sr 3 161165 60437 (by norm_num) (by norm_num) (B 60437 (by norm_num) (by norm_num) (by norm_num))))
theorem R107447 : Reach 107447 := (sr 1 107447 161171 (by norm_num) (by norm_num) (sr 1 161171 241757 (by norm_num) (by norm_num) (sr 3 241757 90659 (by norm_num) (by norm_num) (B 90659 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107451 : Reach 107451 := (sr 1 107451 161177 (by norm_num) (by norm_num) (sr 2 161177 120883 (by norm_num) (by norm_num) (sr 1 120883 181325 (by norm_num) (by norm_num) (sr 3 181325 67997 (by norm_num) (by norm_num) (B 67997 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107455 : Reach 107455 := (sr 1 107455 161183 (by norm_num) (by norm_num) (sr 1 161183 241775 (by norm_num) (by norm_num) (sr 1 241775 362663 (by norm_num) (by norm_num) (sr 1 362663 543995 (by norm_num) (by norm_num) (sr 1 543995 815993 (by norm_num) (by norm_num) (sr 2 815993 611995 (by norm_num) (by norm_num) (sr 1 611995 917993 (by norm_num) (by norm_num) (sr 2 917993 688495 (by norm_num) (by norm_num) (sr 1 688495 1032743 (by norm_num) (by norm_num) (sr 1 1032743 1549115 (by norm_num) (by norm_num) (sr 1 1549115 2323673 (by norm_num) (by norm_num) (sr 2 2323673 1742755 (by norm_num) (by norm_num) (sr 1 1742755 2614133 (by norm_num) (by norm_num) (sr 5 2614133 245075 (by norm_num) (by norm_num) (sr 1 245075 367613 (by norm_num) (by norm_num) (sr 3 367613 137855 (by norm_num) (by norm_num) (sr 1 137855 206783 (by norm_num) (by norm_num) (sr 1 206783 310175 (by norm_num) (by norm_num) (sr 1 310175 465263 (by norm_num) (by norm_num) (sr 1 465263 697895 (by norm_num) (by norm_num) (sr 1 697895 1046843 (by norm_num) (by norm_num) (sr 1 1046843 1570265 (by norm_num) (by norm_num) (sr 2 1570265 1177699 (by norm_num) (by norm_num) (sr 1 1177699 1766549 (by norm_num) (by norm_num) (sr 6 1766549 82807 (by norm_num) (by norm_num) (B 82807 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))
theorem R107459 : Reach 107459 := (sr 1 107459 161189 (by norm_num) (by norm_num) (sr 4 161189 30223 (by norm_num) (by norm_num) (B 30223 (by norm_num) (by norm_num) (by norm_num))))
theorem R107463 : Reach 107463 := (sr 1 107463 161195 (by norm_num) (by norm_num) (sr 1 161195 241793 (by norm_num) (by norm_num) (sr 2 241793 181345 (by norm_num) (by norm_num) (sr 2 181345 136009 (by norm_num) (by norm_num) (sr 2 136009 102007 (by norm_num) (by norm_num) R102007)))))
theorem R107467 : Reach 107467 := (sr 1 107467 161201 (by norm_num) (by norm_num) (sr 2 161201 120901 (by norm_num) (by norm_num) (sr 4 120901 22669 (by norm_num) (by norm_num) (B 22669 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107471 : Reach 107471 := (sr 1 107471 161207 (by norm_num) (by norm_num) (sr 1 161207 241811 (by norm_num) (by norm_num) (sr 1 241811 362717 (by norm_num) (by norm_num) (sr 3 362717 136019 (by norm_num) (by norm_num) (sr 1 136019 204029 (by norm_num) (by norm_num) (sr 3 204029 76511 (by norm_num) (by norm_num) (B 76511 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107475 : Reach 107475 := (sr 1 107475 161213 (by norm_num) (by norm_num) (sr 3 161213 60455 (by norm_num) (by norm_num) (B 60455 (by norm_num) (by norm_num) (by norm_num))))
theorem R107479 : Reach 107479 := (sr 1 107479 161219 (by norm_num) (by norm_num) (sr 1 161219 241829 (by norm_num) (by norm_num) (sr 4 241829 45343 (by norm_num) (by norm_num) (B 45343 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107483 : Reach 107483 := (sr 1 107483 161225 (by norm_num) (by norm_num) (sr 2 161225 120919 (by norm_num) (by norm_num) (sr 1 120919 181379 (by norm_num) (by norm_num) (sr 1 181379 272069 (by norm_num) (by norm_num) (sr 4 272069 51013 (by norm_num) (by norm_num) (B 51013 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R107487 : Reach 107487 := (sr 1 107487 161231 (by norm_num) (by norm_num) (sr 1 161231 241847 (by norm_num) (by norm_num) (sr 1 241847 362771 (by norm_num) (by norm_num) (sr 1 362771 544157 (by norm_num) (by norm_num) (sr 3 544157 204059 (by norm_num) (by norm_num) (sr 1 204059 306089 (by norm_num) (by norm_num) (sr 2 306089 229567 (by norm_num) (by norm_num) (sr 1 229567 344351 (by norm_num) (by norm_num) (sr 1 344351 516527 (by norm_num) (by norm_num) (sr 1 516527 774791 (by norm_num) (by norm_num) (sr 1 774791 1162187 (by norm_num) (by norm_num) (sr 1 1162187 1743281 (by norm_num) (by norm_num) (sr 2 1743281 1307461 (by norm_num) (by norm_num) (sr 4 1307461 245149 (by norm_num) (by norm_num) (sr 3 245149 91931 (by norm_num) (by norm_num) (B 91931 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R107491 : Reach 107491 := (sr 1 107491 161237 (by norm_num) (by norm_num) (sr 7 161237 3779 (by norm_num) (by norm_num) (B 3779 (by norm_num) (by norm_num) (by norm_num))))
theorem R107495 : Reach 107495 := (sr 1 107495 161243 (by norm_num) (by norm_num) (sr 1 161243 241865 (by norm_num) (by norm_num) (sr 2 241865 181399 (by norm_num) (by norm_num) (sr 1 181399 272099 (by norm_num) (by norm_num) (sr 1 272099 408149 (by norm_num) (by norm_num) (sr 8 408149 4783 (by norm_num) (by norm_num) (B 4783 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107499 : Reach 107499 := (sr 1 107499 161249 (by norm_num) (by norm_num) (sr 2 161249 120937 (by norm_num) (by norm_num) (sr 2 120937 90703 (by norm_num) (by norm_num) (B 90703 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107503 : Reach 107503 := (sr 1 107503 161255 (by norm_num) (by norm_num) (sr 1 161255 241883 (by norm_num) (by norm_num) (sr 1 241883 362825 (by norm_num) (by norm_num) (sr 2 362825 272119 (by norm_num) (by norm_num) (sr 1 272119 408179 (by norm_num) (by norm_num) (sr 1 408179 612269 (by norm_num) (by norm_num) (sr 3 612269 229601 (by norm_num) (by norm_num) (sr 2 229601 172201 (by norm_num) (by norm_num) (sr 2 172201 129151 (by norm_num) (by norm_num) (sr 1 129151 193727 (by norm_num) (by norm_num) (sr 1 193727 290591 (by norm_num) (by norm_num) (sr 1 290591 435887 (by norm_num) (by norm_num) (sr 1 435887 653831 (by norm_num) (by norm_num) (sr 1 653831 980747 (by norm_num) (by norm_num) (sr 1 980747 1471121 (by norm_num) (by norm_num) (sr 2 1471121 1103341 (by norm_num) (by norm_num) (sr 3 1103341 413753 (by norm_num) (by norm_num) (sr 2 413753 310315 (by norm_num) (by norm_num) (sr 1 310315 465473 (by norm_num) (by norm_num) (sr 2 465473 349105 (by norm_num) (by norm_num) (sr 2 349105 261829 (by norm_num) (by norm_num) (sr 4 261829 49093 (by norm_num) (by norm_num) (B 49093 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R107507 : Reach 107507 := (sr 1 107507 161261 (by norm_num) (by norm_num) (sr 3 161261 60473 (by norm_num) (by norm_num) (B 60473 (by norm_num) (by norm_num) (by norm_num))))
theorem R107511 : Reach 107511 := (sr 1 107511 161267 (by norm_num) (by norm_num) (sr 1 161267 241901 (by norm_num) (by norm_num) (sr 3 241901 90713 (by norm_num) (by norm_num) (B 90713 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107515 : Reach 107515 := (sr 1 107515 161273 (by norm_num) (by norm_num) (sr 2 161273 120955 (by norm_num) (by norm_num) (sr 1 120955 181433 (by norm_num) (by norm_num) (sr 2 181433 136075 (by norm_num) (by norm_num) (sr 1 136075 204113 (by norm_num) (by norm_num) (sr 2 204113 153085 (by norm_num) (by norm_num) (sr 3 153085 57407 (by norm_num) (by norm_num) (B 57407 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R107519 : Reach 107519 := (sr 1 107519 161279 (by norm_num) (by norm_num) (sr 1 161279 241919 (by norm_num) (by norm_num) (sr 1 241919 362879 (by norm_num) (by norm_num) (sr 1 362879 544319 (by norm_num) (by norm_num) (sr 1 544319 816479 (by norm_num) (by norm_num) (sr 1 816479 1224719 (by norm_num) (by norm_num) (sr 1 1224719 1837079 (by norm_num) (by norm_num) (sr 1 1837079 2755619 (by norm_num) (by norm_num) (sr 1 2755619 4133429 (by norm_num) (by norm_num) (sr 5 4133429 387509 (by norm_num) (by norm_num) (sr 5 387509 36329 (by norm_num) (by norm_num) (B 36329 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R107523 : Reach 107523 := (sr 1 107523 161285 (by norm_num) (by norm_num) (sr 4 161285 30241 (by norm_num) (by norm_num) (B 30241 (by norm_num) (by norm_num) (by norm_num))))
theorem R107527 : Reach 107527 := (sr 1 107527 161291 (by norm_num) (by norm_num) (sr 1 161291 241937 (by norm_num) (by norm_num) (sr 2 241937 181453 (by norm_num) (by norm_num) (sr 3 181453 68045 (by norm_num) (by norm_num) (B 68045 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107531 : Reach 107531 := (sr 1 107531 161297 (by norm_num) (by norm_num) (sr 2 161297 120973 (by norm_num) (by norm_num) (sr 3 120973 45365 (by norm_num) (by norm_num) (B 45365 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107535 : Reach 107535 := (sr 1 107535 161303 (by norm_num) (by norm_num) (sr 1 161303 241955 (by norm_num) (by norm_num) (sr 1 241955 362933 (by norm_num) (by norm_num) (sr 5 362933 34025 (by norm_num) (by norm_num) (B 34025 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107539 : Reach 107539 := (sr 1 107539 161309 (by norm_num) (by norm_num) (sr 3 161309 60491 (by norm_num) (by norm_num) (B 60491 (by norm_num) (by norm_num) (by norm_num))))
theorem R107543 : Reach 107543 := (sr 1 107543 161315 (by norm_num) (by norm_num) (sr 1 161315 241973 (by norm_num) (by norm_num) (sr 5 241973 22685 (by norm_num) (by norm_num) (B 22685 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107547 : Reach 107547 := (sr 1 107547 161321 (by norm_num) (by norm_num) (sr 2 161321 120991 (by norm_num) (by norm_num) (sr 1 120991 181487 (by norm_num) (by norm_num) (sr 1 181487 272231 (by norm_num) (by norm_num) (sr 1 272231 408347 (by norm_num) (by norm_num) (sr 1 408347 612521 (by norm_num) (by norm_num) (sr 2 612521 459391 (by norm_num) (by norm_num) (sr 1 459391 689087 (by norm_num) (by norm_num) (sr 1 689087 1033631 (by norm_num) (by norm_num) (sr 1 1033631 1550447 (by norm_num) (by norm_num) (sr 1 1550447 2325671 (by norm_num) (by norm_num) (sr 1 2325671 3488507 (by norm_num) (by norm_num) (sr 1 3488507 5232761 (by norm_num) (by norm_num) (sr 2 5232761 3924571 (by norm_num) (by norm_num) (sr 1 3924571 5886857 (by norm_num) (by norm_num) (sr 2 5886857 4415143 (by norm_num) (by norm_num) (sr 1 4415143 6622715 (by norm_num) (by norm_num) (sr 1 6622715 9934073 (by norm_num) (by norm_num) (sr 2 9934073 7450555 (by norm_num) (by norm_num) (sr 1 7450555 11175833 (by norm_num) (by norm_num) (sr 2 11175833 8381875 (by norm_num) (by norm_num) (sr 1 8381875 12572813 (by norm_num) (by norm_num) (sr 3 12572813 4714805 (by norm_num) (by norm_num) (sr 5 4714805 442013 (by norm_num) (by norm_num) (sr 3 442013 165755 (by norm_num) (by norm_num) (sr 1 165755 248633 (by norm_num) (by norm_num) (sr 2 248633 186475 (by norm_num) (by norm_num) (sr 1 186475 279713 (by norm_num) (by norm_num) (sr 2 279713 209785 (by norm_num) (by norm_num) (sr 2 209785 157339 (by norm_num) (by norm_num) (sr 1 157339 236009 (by norm_num) (by norm_num) (sr 2 236009 177007 (by norm_num) (by norm_num) (sr 1 177007 265511 (by norm_num) (by norm_num) (sr 1 265511 398267 (by norm_num) (by norm_num) (sr 1 398267 597401 (by norm_num) (by norm_num) (sr 2 597401 448051 (by norm_num) (by norm_num) (sr 1 448051 672077 (by norm_num) (by norm_num) (sr 3 672077 252029 (by norm_num) (by norm_num) (sr 3 252029 94511 (by norm_num) (by norm_num) (B 94511 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))))))))))))
theorem R107551 : Reach 107551 := (sr 1 107551 161327 (by norm_num) (by norm_num) (sr 1 161327 241991 (by norm_num) (by norm_num) (sr 1 241991 362987 (by norm_num) (by norm_num) (sr 1 362987 544481 (by norm_num) (by norm_num) (sr 2 544481 408361 (by norm_num) (by norm_num) (sr 2 408361 306271 (by norm_num) (by norm_num) (sr 1 306271 459407 (by norm_num) (by norm_num) (sr 1 459407 689111 (by norm_num) (by norm_num) (sr 1 689111 1033667 (by norm_num) (by norm_num) (sr 1 1033667 1550501 (by norm_num) (by norm_num) (sr 4 1550501 290719 (by norm_num) (by norm_num) (sr 1 290719 436079 (by norm_num) (by norm_num) (sr 1 436079 654119 (by norm_num) (by norm_num) (sr 1 654119 981179 (by norm_num) (by norm_num) (sr 1 981179 1471769 (by norm_num) (by norm_num) (sr 2 1471769 1103827 (by norm_num) (by norm_num) (sr 1 1103827 1655741 (by norm_num) (by norm_num) (sr 3 1655741 620903 (by norm_num) (by norm_num) (sr 1 620903 931355 (by norm_num) (by norm_num) (sr 1 931355 1397033 (by norm_num) (by norm_num) (sr 2 1397033 1047775 (by norm_num) (by norm_num) (sr 1 1047775 1571663 (by norm_num) (by norm_num) (sr 1 1571663 2357495 (by norm_num) (by norm_num) (sr 1 2357495 3536243 (by norm_num) (by norm_num) (sr 1 3536243 5304365 (by norm_num) (by norm_num) (sr 3 5304365 1989137 (by norm_num) (by norm_num) (sr 2 1989137 1491853 (by norm_num) (by norm_num) (sr 3 1491853 559445 (by norm_num) (by norm_num) (sr 10 559445 1639 (by norm_num) (by norm_num) (B 1639 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))
theorem R107555 : Reach 107555 := (sr 1 107555 161333 (by norm_num) (by norm_num) (sr 5 161333 15125 (by norm_num) (by norm_num) (B 15125 (by norm_num) (by norm_num) (by norm_num))))
theorem R107559 : Reach 107559 := (sr 1 107559 161339 (by norm_num) (by norm_num) (sr 1 161339 242009 (by norm_num) (by norm_num) (sr 2 242009 181507 (by norm_num) (by norm_num) (sr 1 181507 272261 (by norm_num) (by norm_num) (sr 4 272261 51049 (by norm_num) (by norm_num) (B 51049 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R107563 : Reach 107563 := (sr 1 107563 161345 (by norm_num) (by norm_num) (sr 2 161345 121009 (by norm_num) (by norm_num) (sr 2 121009 90757 (by norm_num) (by norm_num) (B 90757 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107567 : Reach 107567 := (sr 1 107567 161351 (by norm_num) (by norm_num) (sr 1 161351 242027 (by norm_num) (by norm_num) (sr 1 242027 363041 (by norm_num) (by norm_num) (sr 2 363041 272281 (by norm_num) (by norm_num) (sr 2 272281 204211 (by norm_num) (by norm_num) (sr 1 204211 306317 (by norm_num) (by norm_num) (sr 3 306317 114869 (by norm_num) (by norm_num) (sr 5 114869 10769 (by norm_num) (by norm_num) (B 10769 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R107571 : Reach 107571 := (sr 1 107571 161357 (by norm_num) (by norm_num) (sr 3 161357 60509 (by norm_num) (by norm_num) (B 60509 (by norm_num) (by norm_num) (by norm_num))))
theorem R107575 : Reach 107575 := (sr 1 107575 161363 (by norm_num) (by norm_num) (sr 1 161363 242045 (by norm_num) (by norm_num) (sr 3 242045 90767 (by norm_num) (by norm_num) (B 90767 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107579 : Reach 107579 := (sr 1 107579 161369 (by norm_num) (by norm_num) (sr 2 161369 121027 (by norm_num) (by norm_num) (sr 1 121027 181541 (by norm_num) (by norm_num) (sr 4 181541 34039 (by norm_num) (by norm_num) (B 34039 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107583 : Reach 107583 := (sr 1 107583 161375 (by norm_num) (by norm_num) (sr 1 161375 242063 (by norm_num) (by norm_num) (sr 1 242063 363095 (by norm_num) (by norm_num) (sr 1 363095 544643 (by norm_num) (by norm_num) (sr 1 544643 816965 (by norm_num) (by norm_num) (sr 4 816965 153181 (by norm_num) (by norm_num) (sr 3 153181 57443 (by norm_num) (by norm_num) (B 57443 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R107587 : Reach 107587 := (sr 1 107587 161381 (by norm_num) (by norm_num) (sr 4 161381 30259 (by norm_num) (by norm_num) (B 30259 (by norm_num) (by norm_num) (by norm_num))))
theorem R107591 : Reach 107591 := (sr 1 107591 161387 (by norm_num) (by norm_num) (sr 1 161387 242081 (by norm_num) (by norm_num) (sr 2 242081 181561 (by norm_num) (by norm_num) (sr 2 181561 136171 (by norm_num) (by norm_num) (sr 1 136171 204257 (by norm_num) (by norm_num) (sr 2 204257 153193 (by norm_num) (by norm_num) (sr 2 153193 114895 (by norm_num) (by norm_num) (sr 1 114895 172343 (by norm_num) (by norm_num) (sr 1 172343 258515 (by norm_num) (by norm_num) (sr 1 258515 387773 (by norm_num) (by norm_num) (sr 3 387773 145415 (by norm_num) (by norm_num) (sr 1 145415 218123 (by norm_num) (by norm_num) (sr 1 218123 327185 (by norm_num) (by norm_num) (sr 2 327185 245389 (by norm_num) (by norm_num) (sr 3 245389 92021 (by norm_num) (by norm_num) (B 92021 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R107595 : Reach 107595 := (sr 1 107595 161393 (by norm_num) (by norm_num) (sr 2 161393 121045 (by norm_num) (by norm_num) (sr 7 121045 2837 (by norm_num) (by norm_num) (B 2837 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107599 : Reach 107599 := (sr 1 107599 161399 (by norm_num) (by norm_num) (sr 1 161399 242099 (by norm_num) (by norm_num) (sr 1 242099 363149 (by norm_num) (by norm_num) (sr 3 363149 136181 (by norm_num) (by norm_num) (sr 5 136181 12767 (by norm_num) (by norm_num) (B 12767 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R107603 : Reach 107603 := (sr 1 107603 161405 (by norm_num) (by norm_num) (sr 3 161405 60527 (by norm_num) (by norm_num) (B 60527 (by norm_num) (by norm_num) (by norm_num))))
theorem R107607 : Reach 107607 := (sr 1 107607 161411 (by norm_num) (by norm_num) (sr 1 161411 242117 (by norm_num) (by norm_num) (sr 4 242117 45397 (by norm_num) (by norm_num) (B 45397 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107611 : Reach 107611 := (sr 1 107611 161417 (by norm_num) (by norm_num) (sr 2 161417 121063 (by norm_num) (by norm_num) (sr 1 121063 181595 (by norm_num) (by norm_num) (sr 1 181595 272393 (by norm_num) (by norm_num) (sr 2 272393 204295 (by norm_num) (by norm_num) (sr 1 204295 306443 (by norm_num) (by norm_num) (sr 1 306443 459665 (by norm_num) (by norm_num) (sr 2 459665 344749 (by norm_num) (by norm_num) (sr 3 344749 129281 (by norm_num) (by norm_num) (sr 2 129281 96961 (by norm_num) (by norm_num) (B 96961 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R107615 : Reach 107615 := (sr 1 107615 161423 (by norm_num) (by norm_num) (sr 1 161423 242135 (by norm_num) (by norm_num) (sr 1 242135 363203 (by norm_num) (by norm_num) (sr 1 363203 544805 (by norm_num) (by norm_num) (sr 4 544805 102151 (by norm_num) (by norm_num) R102151)))))
theorem R107619 : Reach 107619 := (sr 1 107619 161429 (by norm_num) (by norm_num) (sr 6 161429 7567 (by norm_num) (by norm_num) (B 7567 (by norm_num) (by norm_num) (by norm_num))))
theorem R107623 : Reach 107623 := (sr 1 107623 161435 (by norm_num) (by norm_num) (sr 1 161435 242153 (by norm_num) (by norm_num) (sr 2 242153 181615 (by norm_num) (by norm_num) (sr 1 181615 272423 (by norm_num) (by norm_num) (sr 1 272423 408635 (by norm_num) (by norm_num) (sr 1 408635 612953 (by norm_num) (by norm_num) (sr 2 612953 459715 (by norm_num) (by norm_num) (sr 1 459715 689573 (by norm_num) (by norm_num) (sr 4 689573 129295 (by norm_num) (by norm_num) (sr 1 129295 193943 (by norm_num) (by norm_num) (sr 1 193943 290915 (by norm_num) (by norm_num) (sr 1 290915 436373 (by norm_num) (by norm_num) (sr 6 436373 20455 (by norm_num) (by norm_num) (B 20455 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R107627 : Reach 107627 := (sr 1 107627 161441 (by norm_num) (by norm_num) (sr 2 161441 121081 (by norm_num) (by norm_num) (sr 2 121081 90811 (by norm_num) (by norm_num) (B 90811 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107631 : Reach 107631 := (sr 1 107631 161447 (by norm_num) (by norm_num) (sr 1 161447 242171 (by norm_num) (by norm_num) (sr 1 242171 363257 (by norm_num) (by norm_num) (sr 2 363257 272443 (by norm_num) (by norm_num) (sr 1 272443 408665 (by norm_num) (by norm_num) (sr 2 408665 306499 (by norm_num) (by norm_num) (sr 1 306499 459749 (by norm_num) (by norm_num) (sr 4 459749 86203 (by norm_num) (by norm_num) (B 86203 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R107635 : Reach 107635 := (sr 1 107635 161453 (by norm_num) (by norm_num) (sr 3 161453 60545 (by norm_num) (by norm_num) (B 60545 (by norm_num) (by norm_num) (by norm_num))))
theorem R107639 : Reach 107639 := (sr 1 107639 161459 (by norm_num) (by norm_num) (sr 1 161459 242189 (by norm_num) (by norm_num) (sr 3 242189 90821 (by norm_num) (by norm_num) (B 90821 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107643 : Reach 107643 := (sr 1 107643 161465 (by norm_num) (by norm_num) (sr 2 161465 121099 (by norm_num) (by norm_num) (sr 1 121099 181649 (by norm_num) (by norm_num) (sr 2 181649 136237 (by norm_num) (by norm_num) (sr 3 136237 51089 (by norm_num) (by norm_num) (B 51089 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R107647 : Reach 107647 := (sr 1 107647 161471 (by norm_num) (by norm_num) (sr 1 161471 242207 (by norm_num) (by norm_num) (sr 1 242207 363311 (by norm_num) (by norm_num) (sr 1 363311 544967 (by norm_num) (by norm_num) (sr 1 544967 817451 (by norm_num) (by norm_num) (sr 1 817451 1226177 (by norm_num) (by norm_num) (sr 2 1226177 919633 (by norm_num) (by norm_num) (sr 2 919633 689725 (by norm_num) (by norm_num) (sr 3 689725 258647 (by norm_num) (by norm_num) (sr 1 258647 387971 (by norm_num) (by norm_num) (sr 1 387971 581957 (by norm_num) (by norm_num) (sr 4 581957 109117 (by norm_num) (by norm_num) (sr 3 109117 40919 (by norm_num) (by norm_num) (B 40919 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R107651 : Reach 107651 := (sr 1 107651 161477 (by norm_num) (by norm_num) (sr 4 161477 30277 (by norm_num) (by norm_num) (B 30277 (by norm_num) (by norm_num) (by norm_num))))
theorem R107655 : Reach 107655 := (sr 1 107655 161483 (by norm_num) (by norm_num) (sr 1 161483 242225 (by norm_num) (by norm_num) (sr 2 242225 181669 (by norm_num) (by norm_num) (sr 4 181669 34063 (by norm_num) (by norm_num) (B 34063 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107659 : Reach 107659 := (sr 1 107659 161489 (by norm_num) (by norm_num) (sr 2 161489 121117 (by norm_num) (by norm_num) (sr 3 121117 45419 (by norm_num) (by norm_num) (B 45419 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107663 : Reach 107663 := (sr 1 107663 161495 (by norm_num) (by norm_num) (sr 1 161495 242243 (by norm_num) (by norm_num) (sr 1 242243 363365 (by norm_num) (by norm_num) (sr 4 363365 68131 (by norm_num) (by norm_num) (B 68131 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107667 : Reach 107667 := (sr 1 107667 161501 (by norm_num) (by norm_num) (sr 3 161501 60563 (by norm_num) (by norm_num) (B 60563 (by norm_num) (by norm_num) (by norm_num))))
theorem R107671 : Reach 107671 := (sr 1 107671 161507 (by norm_num) (by norm_num) (sr 1 161507 242261 (by norm_num) (by norm_num) (sr 8 242261 2839 (by norm_num) (by norm_num) (B 2839 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107675 : Reach 107675 := (sr 1 107675 161513 (by norm_num) (by norm_num) (sr 2 161513 121135 (by norm_num) (by norm_num) (sr 1 121135 181703 (by norm_num) (by norm_num) (sr 1 181703 272555 (by norm_num) (by norm_num) (sr 1 272555 408833 (by norm_num) (by norm_num) (sr 2 408833 306625 (by norm_num) (by norm_num) (sr 2 306625 229969 (by norm_num) (by norm_num) (sr 2 229969 172477 (by norm_num) (by norm_num) (sr 3 172477 64679 (by norm_num) (by norm_num) (B 64679 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R107679 : Reach 107679 := (sr 1 107679 161519 (by norm_num) (by norm_num) (sr 1 161519 242279 (by norm_num) (by norm_num) (sr 1 242279 363419 (by norm_num) (by norm_num) (sr 1 363419 545129 (by norm_num) (by norm_num) (sr 2 545129 408847 (by norm_num) (by norm_num) (sr 1 408847 613271 (by norm_num) (by norm_num) (sr 1 613271 919907 (by norm_num) (by norm_num) (sr 1 919907 1379861 (by norm_num) (by norm_num) (sr 6 1379861 64681 (by norm_num) (by norm_num) (B 64681 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R107683 : Reach 107683 := (sr 1 107683 161525 (by norm_num) (by norm_num) (sr 5 161525 15143 (by norm_num) (by norm_num) (B 15143 (by norm_num) (by norm_num) (by norm_num))))
theorem R107687 : Reach 107687 := (sr 1 107687 161531 (by norm_num) (by norm_num) (sr 1 161531 242297 (by norm_num) (by norm_num) (sr 2 242297 181723 (by norm_num) (by norm_num) (sr 1 181723 272585 (by norm_num) (by norm_num) (sr 2 272585 204439 (by norm_num) (by norm_num) (sr 1 204439 306659 (by norm_num) (by norm_num) (sr 1 306659 459989 (by norm_num) (by norm_num) (sr 7 459989 10781 (by norm_num) (by norm_num) (B 10781 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R107691 : Reach 107691 := (sr 1 107691 161537 (by norm_num) (by norm_num) (sr 2 161537 121153 (by norm_num) (by norm_num) (sr 2 121153 90865 (by norm_num) (by norm_num) (B 90865 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107695 : Reach 107695 := (sr 1 107695 161543 (by norm_num) (by norm_num) (sr 1 161543 242315 (by norm_num) (by norm_num) (sr 1 242315 363473 (by norm_num) (by norm_num) (sr 2 363473 272605 (by norm_num) (by norm_num) (sr 3 272605 102227 (by norm_num) (by norm_num) R102227)))))
theorem R107699 : Reach 107699 := (sr 1 107699 161549 (by norm_num) (by norm_num) (sr 3 161549 60581 (by norm_num) (by norm_num) (B 60581 (by norm_num) (by norm_num) (by norm_num))))
theorem R107703 : Reach 107703 := (sr 1 107703 161555 (by norm_num) (by norm_num) (sr 1 161555 242333 (by norm_num) (by norm_num) (sr 3 242333 90875 (by norm_num) (by norm_num) (B 90875 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107707 : Reach 107707 := (sr 1 107707 161561 (by norm_num) (by norm_num) (sr 2 161561 121171 (by norm_num) (by norm_num) (sr 1 121171 181757 (by norm_num) (by norm_num) (sr 3 181757 68159 (by norm_num) (by norm_num) (B 68159 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107711 : Reach 107711 := (sr 1 107711 161567 (by norm_num) (by norm_num) (sr 1 161567 242351 (by norm_num) (by norm_num) (sr 1 242351 363527 (by norm_num) (by norm_num) (sr 1 363527 545291 (by norm_num) (by norm_num) (sr 1 545291 817937 (by norm_num) (by norm_num) (sr 2 817937 613453 (by norm_num) (by norm_num) (sr 3 613453 230045 (by norm_num) (by norm_num) (sr 3 230045 86267 (by norm_num) (by norm_num) (B 86267 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R107715 : Reach 107715 := (sr 1 107715 161573 (by norm_num) (by norm_num) (sr 4 161573 30295 (by norm_num) (by norm_num) (B 30295 (by norm_num) (by norm_num) (by norm_num))))
theorem R107719 : Reach 107719 := (sr 1 107719 161579 (by norm_num) (by norm_num) (sr 1 161579 242369 (by norm_num) (by norm_num) (sr 2 242369 181777 (by norm_num) (by norm_num) (sr 2 181777 136333 (by norm_num) (by norm_num) (sr 3 136333 51125 (by norm_num) (by norm_num) (B 51125 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R107723 : Reach 107723 := (sr 1 107723 161585 (by norm_num) (by norm_num) (sr 2 161585 121189 (by norm_num) (by norm_num) (sr 4 121189 22723 (by norm_num) (by norm_num) (B 22723 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107727 : Reach 107727 := (sr 1 107727 161591 (by norm_num) (by norm_num) (sr 1 161591 242387 (by norm_num) (by norm_num) (sr 1 242387 363581 (by norm_num) (by norm_num) (sr 3 363581 136343 (by norm_num) (by norm_num) (sr 1 136343 204515 (by norm_num) (by norm_num) (sr 1 204515 306773 (by norm_num) (by norm_num) (sr 8 306773 3595 (by norm_num) (by norm_num) (B 3595 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R107731 : Reach 107731 := (sr 1 107731 161597 (by norm_num) (by norm_num) (sr 3 161597 60599 (by norm_num) (by norm_num) (B 60599 (by norm_num) (by norm_num) (by norm_num))))
theorem R107735 : Reach 107735 := (sr 1 107735 161603 (by norm_num) (by norm_num) (sr 1 161603 242405 (by norm_num) (by norm_num) (sr 4 242405 45451 (by norm_num) (by norm_num) (B 45451 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107739 : Reach 107739 := (sr 1 107739 161609 (by norm_num) (by norm_num) (sr 2 161609 121207 (by norm_num) (by norm_num) (sr 1 121207 181811 (by norm_num) (by norm_num) (sr 1 181811 272717 (by norm_num) (by norm_num) (sr 3 272717 102269 (by norm_num) (by norm_num) (sr 3 102269 38351 (by norm_num) (by norm_num) (B 38351 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107743 : Reach 107743 := (sr 1 107743 161615 (by norm_num) (by norm_num) (sr 1 161615 242423 (by norm_num) (by norm_num) (sr 1 242423 363635 (by norm_num) (by norm_num) (sr 1 363635 545453 (by norm_num) (by norm_num) (sr 3 545453 204545 (by norm_num) (by norm_num) (sr 2 204545 153409 (by norm_num) (by norm_num) (sr 2 153409 115057 (by norm_num) (by norm_num) (sr 2 115057 86293 (by norm_num) (by norm_num) (B 86293 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R107747 : Reach 107747 := (sr 1 107747 161621 (by norm_num) (by norm_num) (sr 9 161621 947 (by norm_num) (by norm_num) (B 947 (by norm_num) (by norm_num) (by norm_num))))
theorem R107751 : Reach 107751 := (sr 1 107751 161627 (by norm_num) (by norm_num) (sr 1 161627 242441 (by norm_num) (by norm_num) (sr 2 242441 181831 (by norm_num) (by norm_num) (sr 1 181831 272747 (by norm_num) (by norm_num) (sr 1 272747 409121 (by norm_num) (by norm_num) (sr 2 409121 306841 (by norm_num) (by norm_num) (sr 2 306841 230131 (by norm_num) (by norm_num) (sr 1 230131 345197 (by norm_num) (by norm_num) (sr 3 345197 129449 (by norm_num) (by norm_num) (sr 2 129449 97087 (by norm_num) (by norm_num) (B 97087 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R107755 : Reach 107755 := (sr 1 107755 161633 (by norm_num) (by norm_num) (sr 2 161633 121225 (by norm_num) (by norm_num) (sr 2 121225 90919 (by norm_num) (by norm_num) (B 90919 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107759 : Reach 107759 := (sr 1 107759 161639 (by norm_num) (by norm_num) (sr 1 161639 242459 (by norm_num) (by norm_num) (sr 1 242459 363689 (by norm_num) (by norm_num) (sr 2 363689 272767 (by norm_num) (by norm_num) (sr 1 272767 409151 (by norm_num) (by norm_num) (sr 1 409151 613727 (by norm_num) (by norm_num) (sr 1 613727 920591 (by norm_num) (by norm_num) (sr 1 920591 1380887 (by norm_num) (by norm_num) (sr 1 1380887 2071331 (by norm_num) (by norm_num) (sr 1 2071331 3106997 (by norm_num) (by norm_num) (sr 5 3106997 291281 (by norm_num) (by norm_num) (sr 2 291281 218461 (by norm_num) (by norm_num) (sr 3 218461 81923 (by norm_num) (by norm_num) (B 81923 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R107763 : Reach 107763 := (sr 1 107763 161645 (by norm_num) (by norm_num) (sr 3 161645 60617 (by norm_num) (by norm_num) (B 60617 (by norm_num) (by norm_num) (by norm_num))))
theorem R107767 : Reach 107767 := (sr 1 107767 161651 (by norm_num) (by norm_num) (sr 1 161651 242477 (by norm_num) (by norm_num) (sr 3 242477 90929 (by norm_num) (by norm_num) (B 90929 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107771 : Reach 107771 := (sr 1 107771 161657 (by norm_num) (by norm_num) (sr 2 161657 121243 (by norm_num) (by norm_num) (sr 1 121243 181865 (by norm_num) (by norm_num) (sr 2 181865 136399 (by norm_num) (by norm_num) (sr 1 136399 204599 (by norm_num) (by norm_num) (sr 1 204599 306899 (by norm_num) (by norm_num) (sr 1 306899 460349 (by norm_num) (by norm_num) (sr 3 460349 172631 (by norm_num) (by norm_num) (sr 1 172631 258947 (by norm_num) (by norm_num) (sr 1 258947 388421 (by norm_num) (by norm_num) (sr 4 388421 72829 (by norm_num) (by norm_num) (B 72829 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R107775 : Reach 107775 := (sr 1 107775 161663 (by norm_num) (by norm_num) (sr 1 161663 242495 (by norm_num) (by norm_num) (sr 1 242495 363743 (by norm_num) (by norm_num) (sr 1 363743 545615 (by norm_num) (by norm_num) (sr 1 545615 818423 (by norm_num) (by norm_num) (sr 1 818423 1227635 (by norm_num) (by norm_num) (sr 1 1227635 1841453 (by norm_num) (by norm_num) (sr 3 1841453 690545 (by norm_num) (by norm_num) (sr 2 690545 517909 (by norm_num) (by norm_num) (sr 6 517909 24277 (by norm_num) (by norm_num) (B 24277 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R107779 : Reach 107779 := (sr 1 107779 161669 (by norm_num) (by norm_num) (sr 4 161669 30313 (by norm_num) (by norm_num) (B 30313 (by norm_num) (by norm_num) (by norm_num))))
theorem R107783 : Reach 107783 := (sr 1 107783 161675 (by norm_num) (by norm_num) (sr 1 161675 242513 (by norm_num) (by norm_num) (sr 2 242513 181885 (by norm_num) (by norm_num) (sr 3 181885 68207 (by norm_num) (by norm_num) (B 68207 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107787 : Reach 107787 := (sr 1 107787 161681 (by norm_num) (by norm_num) (sr 2 161681 121261 (by norm_num) (by norm_num) (sr 3 121261 45473 (by norm_num) (by norm_num) (B 45473 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107791 : Reach 107791 := (sr 1 107791 161687 (by norm_num) (by norm_num) (sr 1 161687 242531 (by norm_num) (by norm_num) (sr 1 242531 363797 (by norm_num) (by norm_num) (sr 6 363797 17053 (by norm_num) (by norm_num) (B 17053 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107795 : Reach 107795 := (sr 1 107795 161693 (by norm_num) (by norm_num) (sr 3 161693 60635 (by norm_num) (by norm_num) (B 60635 (by norm_num) (by norm_num) (by norm_num))))
theorem R107799 : Reach 107799 := (sr 1 107799 161699 (by norm_num) (by norm_num) (sr 1 161699 242549 (by norm_num) (by norm_num) (sr 5 242549 22739 (by norm_num) (by norm_num) (B 22739 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107803 : Reach 107803 := (sr 1 107803 161705 (by norm_num) (by norm_num) (sr 2 161705 121279 (by norm_num) (by norm_num) (sr 1 121279 181919 (by norm_num) (by norm_num) (sr 1 181919 272879 (by norm_num) (by norm_num) (sr 1 272879 409319 (by norm_num) (by norm_num) (sr 1 409319 613979 (by norm_num) (by norm_num) (sr 1 613979 920969 (by norm_num) (by norm_num) (sr 2 920969 690727 (by norm_num) (by norm_num) (sr 1 690727 1036091 (by norm_num) (by norm_num) (sr 1 1036091 1554137 (by norm_num) (by norm_num) (sr 2 1554137 1165603 (by norm_num) (by norm_num) (sr 1 1165603 1748405 (by norm_num) (by norm_num) (sr 5 1748405 163913 (by norm_num) (by norm_num) (sr 2 163913 122935 (by norm_num) (by norm_num) (sr 1 122935 184403 (by norm_num) (by norm_num) (sr 1 184403 276605 (by norm_num) (by norm_num) (sr 3 276605 103727 (by norm_num) (by norm_num) R103727)))))))))))))))))
theorem R107807 : Reach 107807 := (sr 1 107807 161711 (by norm_num) (by norm_num) (sr 1 161711 242567 (by norm_num) (by norm_num) (sr 1 242567 363851 (by norm_num) (by norm_num) (sr 1 363851 545777 (by norm_num) (by norm_num) (sr 2 545777 409333 (by norm_num) (by norm_num) (sr 5 409333 38375 (by norm_num) (by norm_num) (B 38375 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107811 : Reach 107811 := (sr 1 107811 161717 (by norm_num) (by norm_num) (sr 5 161717 15161 (by norm_num) (by norm_num) (B 15161 (by norm_num) (by norm_num) (by norm_num))))
theorem R107815 : Reach 107815 := (sr 1 107815 161723 (by norm_num) (by norm_num) (sr 1 161723 242585 (by norm_num) (by norm_num) (sr 2 242585 181939 (by norm_num) (by norm_num) (sr 1 181939 272909 (by norm_num) (by norm_num) (sr 3 272909 102341 (by norm_num) (by norm_num) (sr 4 102341 19189 (by norm_num) (by norm_num) (B 19189 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107819 : Reach 107819 := (sr 1 107819 161729 (by norm_num) (by norm_num) (sr 2 161729 121297 (by norm_num) (by norm_num) (sr 2 121297 90973 (by norm_num) (by norm_num) (B 90973 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107823 : Reach 107823 := (sr 1 107823 161735 (by norm_num) (by norm_num) (sr 1 161735 242603 (by norm_num) (by norm_num) (sr 1 242603 363905 (by norm_num) (by norm_num) (sr 2 363905 272929 (by norm_num) (by norm_num) (sr 2 272929 204697 (by norm_num) (by norm_num) (sr 2 204697 153523 (by norm_num) (by norm_num) (sr 1 153523 230285 (by norm_num) (by norm_num) (sr 3 230285 86357 (by norm_num) (by norm_num) (B 86357 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R107827 : Reach 107827 := (sr 1 107827 161741 (by norm_num) (by norm_num) (sr 3 161741 60653 (by norm_num) (by norm_num) (B 60653 (by norm_num) (by norm_num) (by norm_num))))
theorem R107831 : Reach 107831 := (sr 1 107831 161747 (by norm_num) (by norm_num) (sr 1 161747 242621 (by norm_num) (by norm_num) (sr 3 242621 90983 (by norm_num) (by norm_num) (B 90983 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107835 : Reach 107835 := (sr 1 107835 161753 (by norm_num) (by norm_num) (sr 2 161753 121315 (by norm_num) (by norm_num) (sr 1 121315 181973 (by norm_num) (by norm_num) (sr 7 181973 4265 (by norm_num) (by norm_num) (B 4265 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107839 : Reach 107839 := (sr 1 107839 161759 (by norm_num) (by norm_num) (sr 1 161759 242639 (by norm_num) (by norm_num) (sr 1 242639 363959 (by norm_num) (by norm_num) (sr 1 363959 545939 (by norm_num) (by norm_num) (sr 1 545939 818909 (by norm_num) (by norm_num) (sr 3 818909 307091 (by norm_num) (by norm_num) (sr 1 307091 460637 (by norm_num) (by norm_num) (sr 3 460637 172739 (by norm_num) (by norm_num) (sr 1 172739 259109 (by norm_num) (by norm_num) (sr 4 259109 48583 (by norm_num) (by norm_num) (B 48583 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R107843 : Reach 107843 := (sr 1 107843 161765 (by norm_num) (by norm_num) (sr 4 161765 30331 (by norm_num) (by norm_num) (B 30331 (by norm_num) (by norm_num) (by norm_num))))
theorem R107847 : Reach 107847 := (sr 1 107847 161771 (by norm_num) (by norm_num) (sr 1 161771 242657 (by norm_num) (by norm_num) (sr 2 242657 181993 (by norm_num) (by norm_num) (sr 2 181993 136495 (by norm_num) (by norm_num) (sr 1 136495 204743 (by norm_num) (by norm_num) (sr 1 204743 307115 (by norm_num) (by norm_num) (sr 1 307115 460673 (by norm_num) (by norm_num) (sr 2 460673 345505 (by norm_num) (by norm_num) (sr 2 345505 259129 (by norm_num) (by norm_num) (sr 2 259129 194347 (by norm_num) (by norm_num) (sr 1 194347 291521 (by norm_num) (by norm_num) (sr 2 291521 218641 (by norm_num) (by norm_num) (sr 2 218641 163981 (by norm_num) (by norm_num) (sr 3 163981 61493 (by norm_num) (by norm_num) (B 61493 (by norm_num) (by norm_num) (by norm_num))))))))))))))))
theorem R107851 : Reach 107851 := (sr 1 107851 161777 (by norm_num) (by norm_num) (sr 2 161777 121333 (by norm_num) (by norm_num) (sr 5 121333 11375 (by norm_num) (by norm_num) (B 11375 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107855 : Reach 107855 := (sr 1 107855 161783 (by norm_num) (by norm_num) (sr 1 161783 242675 (by norm_num) (by norm_num) (sr 1 242675 364013 (by norm_num) (by norm_num) (sr 3 364013 136505 (by norm_num) (by norm_num) (sr 2 136505 102379 (by norm_num) (by norm_num) R102379)))))
theorem R107859 : Reach 107859 := (sr 1 107859 161789 (by norm_num) (by norm_num) (sr 3 161789 60671 (by norm_num) (by norm_num) (B 60671 (by norm_num) (by norm_num) (by norm_num))))
theorem R107863 : Reach 107863 := (sr 1 107863 161795 (by norm_num) (by norm_num) (sr 1 161795 242693 (by norm_num) (by norm_num) (sr 4 242693 45505 (by norm_num) (by norm_num) (B 45505 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107867 : Reach 107867 := (sr 1 107867 161801 (by norm_num) (by norm_num) (sr 2 161801 121351 (by norm_num) (by norm_num) (sr 1 121351 182027 (by norm_num) (by norm_num) (sr 1 182027 273041 (by norm_num) (by norm_num) (sr 2 273041 204781 (by norm_num) (by norm_num) (sr 3 204781 76793 (by norm_num) (by norm_num) (B 76793 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107871 : Reach 107871 := (sr 1 107871 161807 (by norm_num) (by norm_num) (sr 1 161807 242711 (by norm_num) (by norm_num) (sr 1 242711 364067 (by norm_num) (by norm_num) (sr 1 364067 546101 (by norm_num) (by norm_num) (sr 5 546101 51197 (by norm_num) (by norm_num) (B 51197 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R107875 : Reach 107875 := (sr 1 107875 161813 (by norm_num) (by norm_num) (sr 6 161813 7585 (by norm_num) (by norm_num) (B 7585 (by norm_num) (by norm_num) (by norm_num))))
theorem R107879 : Reach 107879 := (sr 1 107879 161819 (by norm_num) (by norm_num) (sr 1 161819 242729 (by norm_num) (by norm_num) (sr 2 242729 182047 (by norm_num) (by norm_num) (sr 1 182047 273071 (by norm_num) (by norm_num) (sr 1 273071 409607 (by norm_num) (by norm_num) (sr 1 409607 614411 (by norm_num) (by norm_num) (sr 1 614411 921617 (by norm_num) (by norm_num) (sr 2 921617 691213 (by norm_num) (by norm_num) (sr 3 691213 259205 (by norm_num) (by norm_num) (sr 4 259205 48601 (by norm_num) (by norm_num) (B 48601 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R107883 : Reach 107883 := (sr 1 107883 161825 (by norm_num) (by norm_num) (sr 2 161825 121369 (by norm_num) (by norm_num) (sr 2 121369 91027 (by norm_num) (by norm_num) (B 91027 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107887 : Reach 107887 := (sr 1 107887 161831 (by norm_num) (by norm_num) (sr 1 161831 242747 (by norm_num) (by norm_num) (sr 1 242747 364121 (by norm_num) (by norm_num) (sr 2 364121 273091 (by norm_num) (by norm_num) (sr 1 273091 409637 (by norm_num) (by norm_num) (sr 4 409637 76807 (by norm_num) (by norm_num) (B 76807 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107891 : Reach 107891 := (sr 1 107891 161837 (by norm_num) (by norm_num) (sr 3 161837 60689 (by norm_num) (by norm_num) (B 60689 (by norm_num) (by norm_num) (by norm_num))))
theorem R107895 : Reach 107895 := (sr 1 107895 161843 (by norm_num) (by norm_num) (sr 1 161843 242765 (by norm_num) (by norm_num) (sr 3 242765 91037 (by norm_num) (by norm_num) (B 91037 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107899 : Reach 107899 := (sr 1 107899 161849 (by norm_num) (by norm_num) (sr 2 161849 121387 (by norm_num) (by norm_num) (sr 1 121387 182081 (by norm_num) (by norm_num) (sr 2 182081 136561 (by norm_num) (by norm_num) (sr 2 136561 102421 (by norm_num) (by norm_num) (sr 6 102421 4801 (by norm_num) (by norm_num) (B 4801 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107903 : Reach 107903 := (sr 1 107903 161855 (by norm_num) (by norm_num) (sr 1 161855 242783 (by norm_num) (by norm_num) (sr 1 242783 364175 (by norm_num) (by norm_num) (sr 1 364175 546263 (by norm_num) (by norm_num) (sr 1 546263 819395 (by norm_num) (by norm_num) (sr 1 819395 1229093 (by norm_num) (by norm_num) (sr 4 1229093 230455 (by norm_num) (by norm_num) (sr 1 230455 345683 (by norm_num) (by norm_num) (sr 1 345683 518525 (by norm_num) (by norm_num) (sr 3 518525 194447 (by norm_num) (by norm_num) (sr 1 194447 291671 (by norm_num) (by norm_num) (sr 1 291671 437507 (by norm_num) (by norm_num) (sr 1 437507 656261 (by norm_num) (by norm_num) (sr 4 656261 123049 (by norm_num) (by norm_num) (sr 2 123049 92287 (by norm_num) (by norm_num) (B 92287 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R107907 : Reach 107907 := (sr 1 107907 161861 (by norm_num) (by norm_num) (sr 4 161861 30349 (by norm_num) (by norm_num) (B 30349 (by norm_num) (by norm_num) (by norm_num))))
theorem R107911 : Reach 107911 := (sr 1 107911 161867 (by norm_num) (by norm_num) (sr 1 161867 242801 (by norm_num) (by norm_num) (sr 2 242801 182101 (by norm_num) (by norm_num) (sr 9 182101 1067 (by norm_num) (by norm_num) (B 1067 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107915 : Reach 107915 := (sr 1 107915 161873 (by norm_num) (by norm_num) (sr 2 161873 121405 (by norm_num) (by norm_num) (sr 3 121405 45527 (by norm_num) (by norm_num) (B 45527 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107919 : Reach 107919 := (sr 1 107919 161879 (by norm_num) (by norm_num) (sr 1 161879 242819 (by norm_num) (by norm_num) (sr 1 242819 364229 (by norm_num) (by norm_num) (sr 4 364229 68293 (by norm_num) (by norm_num) (B 68293 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107923 : Reach 107923 := (sr 1 107923 161885 (by norm_num) (by norm_num) (sr 3 161885 60707 (by norm_num) (by norm_num) (B 60707 (by norm_num) (by norm_num) (by norm_num))))
theorem R107927 : Reach 107927 := (sr 1 107927 161891 (by norm_num) (by norm_num) (sr 1 161891 242837 (by norm_num) (by norm_num) (sr 6 242837 11383 (by norm_num) (by norm_num) (B 11383 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107931 : Reach 107931 := (sr 1 107931 161897 (by norm_num) (by norm_num) (sr 2 161897 121423 (by norm_num) (by norm_num) (sr 1 121423 182135 (by norm_num) (by norm_num) (sr 1 182135 273203 (by norm_num) (by norm_num) (sr 1 273203 409805 (by norm_num) (by norm_num) (sr 3 409805 153677 (by norm_num) (by norm_num) (sr 3 153677 57629 (by norm_num) (by norm_num) (B 57629 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R107935 : Reach 107935 := (sr 1 107935 161903 (by norm_num) (by norm_num) (sr 1 161903 242855 (by norm_num) (by norm_num) (sr 1 242855 364283 (by norm_num) (by norm_num) (sr 1 364283 546425 (by norm_num) (by norm_num) (sr 2 546425 409819 (by norm_num) (by norm_num) (sr 1 409819 614729 (by norm_num) (by norm_num) (sr 2 614729 461047 (by norm_num) (by norm_num) (sr 1 461047 691571 (by norm_num) (by norm_num) (sr 1 691571 1037357 (by norm_num) (by norm_num) (sr 3 1037357 389009 (by norm_num) (by norm_num) (sr 2 389009 291757 (by norm_num) (by norm_num) (sr 3 291757 109409 (by norm_num) (by norm_num) (sr 2 109409 82057 (by norm_num) (by norm_num) (B 82057 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R107939 : Reach 107939 := (sr 1 107939 161909 (by norm_num) (by norm_num) (sr 5 161909 15179 (by norm_num) (by norm_num) (B 15179 (by norm_num) (by norm_num) (by norm_num))))
theorem R107943 : Reach 107943 := (sr 1 107943 161915 (by norm_num) (by norm_num) (sr 1 161915 242873 (by norm_num) (by norm_num) (sr 2 242873 182155 (by norm_num) (by norm_num) (sr 1 182155 273233 (by norm_num) (by norm_num) (sr 2 273233 204925 (by norm_num) (by norm_num) (sr 3 204925 76847 (by norm_num) (by norm_num) (B 76847 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107947 : Reach 107947 := (sr 1 107947 161921 (by norm_num) (by norm_num) (sr 2 161921 121441 (by norm_num) (by norm_num) (sr 2 121441 91081 (by norm_num) (by norm_num) (B 91081 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107951 : Reach 107951 := (sr 1 107951 161927 (by norm_num) (by norm_num) (sr 1 161927 242891 (by norm_num) (by norm_num) (sr 1 242891 364337 (by norm_num) (by norm_num) (sr 2 364337 273253 (by norm_num) (by norm_num) (sr 4 273253 51235 (by norm_num) (by norm_num) (B 51235 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R107955 : Reach 107955 := (sr 1 107955 161933 (by norm_num) (by norm_num) (sr 3 161933 60725 (by norm_num) (by norm_num) (B 60725 (by norm_num) (by norm_num) (by norm_num))))
theorem R107959 : Reach 107959 := (sr 1 107959 161939 (by norm_num) (by norm_num) (sr 1 161939 242909 (by norm_num) (by norm_num) (sr 3 242909 91091 (by norm_num) (by norm_num) (B 91091 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107963 : Reach 107963 := (sr 1 107963 161945 (by norm_num) (by norm_num) (sr 2 161945 121459 (by norm_num) (by norm_num) (sr 1 121459 182189 (by norm_num) (by norm_num) (sr 3 182189 68321 (by norm_num) (by norm_num) (B 68321 (by norm_num) (by norm_num) (by norm_num))))))
theorem R107967 : Reach 107967 := (sr 1 107967 161951 (by norm_num) (by norm_num) (sr 1 161951 242927 (by norm_num) (by norm_num) (sr 1 242927 364391 (by norm_num) (by norm_num) (sr 1 364391 546587 (by norm_num) (by norm_num) (sr 1 546587 819881 (by norm_num) (by norm_num) (sr 2 819881 614911 (by norm_num) (by norm_num) (sr 1 614911 922367 (by norm_num) (by norm_num) (sr 1 922367 1383551 (by norm_num) (by norm_num) (sr 1 1383551 2075327 (by norm_num) (by norm_num) (sr 1 2075327 3112991 (by norm_num) (by norm_num) (sr 1 3112991 4669487 (by norm_num) (by norm_num) (sr 1 4669487 7004231 (by norm_num) (by norm_num) (sr 1 7004231 10506347 (by norm_num) (by norm_num) (sr 1 10506347 15759521 (by norm_num) (by norm_num) (sr 2 15759521 11819641 (by norm_num) (by norm_num) (sr 2 11819641 8864731 (by norm_num) (by norm_num) (sr 1 8864731 13297097 (by norm_num) (by norm_num) (sr 2 13297097 9972823 (by norm_num) (by norm_num) (sr 1 9972823 14959235 (by norm_num) (by norm_num) (sr 1 14959235 22438853 (by norm_num) (by norm_num) (sr 4 22438853 4207285 (by norm_num) (by norm_num) (sr 5 4207285 394433 (by norm_num) (by norm_num) (sr 2 394433 295825 (by norm_num) (by norm_num) (sr 2 295825 221869 (by norm_num) (by norm_num) (sr 3 221869 83201 (by norm_num) (by norm_num) (B 83201 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))
theorem R107971 : Reach 107971 := (sr 1 107971 161957 (by norm_num) (by norm_num) (sr 4 161957 30367 (by norm_num) (by norm_num) (B 30367 (by norm_num) (by norm_num) (by norm_num))))
theorem R107975 : Reach 107975 := (sr 1 107975 161963 (by norm_num) (by norm_num) (sr 1 161963 242945 (by norm_num) (by norm_num) (sr 2 242945 182209 (by norm_num) (by norm_num) (sr 2 182209 136657 (by norm_num) (by norm_num) (sr 2 136657 102493 (by norm_num) (by norm_num) (sr 3 102493 38435 (by norm_num) (by norm_num) (B 38435 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R107979 : Reach 107979 := (sr 1 107979 161969 (by norm_num) (by norm_num) (sr 2 161969 121477 (by norm_num) (by norm_num) (sr 4 121477 22777 (by norm_num) (by norm_num) (B 22777 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107983 : Reach 107983 := (sr 1 107983 161975 (by norm_num) (by norm_num) (sr 1 161975 242963 (by norm_num) (by norm_num) (sr 1 242963 364445 (by norm_num) (by norm_num) (sr 3 364445 136667 (by norm_num) (by norm_num) (sr 1 136667 205001 (by norm_num) (by norm_num) (sr 2 205001 153751 (by norm_num) (by norm_num) (sr 1 153751 230627 (by norm_num) (by norm_num) (sr 1 230627 345941 (by norm_num) (by norm_num) (sr 9 345941 2027 (by norm_num) (by norm_num) (B 2027 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R107987 : Reach 107987 := (sr 1 107987 161981 (by norm_num) (by norm_num) (sr 3 161981 60743 (by norm_num) (by norm_num) (B 60743 (by norm_num) (by norm_num) (by norm_num))))
theorem R107991 : Reach 107991 := (sr 1 107991 161987 (by norm_num) (by norm_num) (sr 1 161987 242981 (by norm_num) (by norm_num) (sr 4 242981 45559 (by norm_num) (by norm_num) (B 45559 (by norm_num) (by norm_num) (by norm_num)))))
theorem R107995 : Reach 107995 := (sr 1 107995 161993 (by norm_num) (by norm_num) (sr 2 161993 121495 (by norm_num) (by norm_num) (sr 1 121495 182243 (by norm_num) (by norm_num) (sr 1 182243 273365 (by norm_num) (by norm_num) (sr 7 273365 6407 (by norm_num) (by norm_num) (B 6407 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R107999 : Reach 107999 := (sr 1 107999 161999 (by norm_num) (by norm_num) (sr 1 161999 242999 (by norm_num) (by norm_num) (sr 1 242999 364499 (by norm_num) (by norm_num) (sr 1 364499 546749 (by norm_num) (by norm_num) (sr 3 546749 205031 (by norm_num) (by norm_num) (sr 1 205031 307547 (by norm_num) (by norm_num) (sr 1 307547 461321 (by norm_num) (by norm_num) (sr 2 461321 345991 (by norm_num) (by norm_num) (sr 1 345991 518987 (by norm_num) (by norm_num) (sr 1 518987 778481 (by norm_num) (by norm_num) (sr 2 778481 583861 (by norm_num) (by norm_num) (sr 5 583861 54737 (by norm_num) (by norm_num) (B 54737 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R108003 : Reach 108003 := (sr 1 108003 162005 (by norm_num) (by norm_num) (sr 7 162005 3797 (by norm_num) (by norm_num) (B 3797 (by norm_num) (by norm_num) (by norm_num))))
theorem R108007 : Reach 108007 := (sr 1 108007 162011 (by norm_num) (by norm_num) (sr 1 162011 243017 (by norm_num) (by norm_num) (sr 2 243017 182263 (by norm_num) (by norm_num) (sr 1 182263 273395 (by norm_num) (by norm_num) (sr 1 273395 410093 (by norm_num) (by norm_num) (sr 3 410093 153785 (by norm_num) (by norm_num) (sr 2 153785 115339 (by norm_num) (by norm_num) (sr 1 115339 173009 (by norm_num) (by norm_num) (sr 2 173009 129757 (by norm_num) (by norm_num) (sr 3 129757 48659 (by norm_num) (by norm_num) (B 48659 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R108011 : Reach 108011 := (sr 1 108011 162017 (by norm_num) (by norm_num) (sr 2 162017 121513 (by norm_num) (by norm_num) (sr 2 121513 91135 (by norm_num) (by norm_num) (B 91135 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108015 : Reach 108015 := (sr 1 108015 162023 (by norm_num) (by norm_num) (sr 1 162023 243035 (by norm_num) (by norm_num) (sr 1 243035 364553 (by norm_num) (by norm_num) (sr 2 364553 273415 (by norm_num) (by norm_num) (sr 1 273415 410123 (by norm_num) (by norm_num) (sr 1 410123 615185 (by norm_num) (by norm_num) (sr 2 615185 461389 (by norm_num) (by norm_num) (sr 3 461389 173021 (by norm_num) (by norm_num) (sr 3 173021 64883 (by norm_num) (by norm_num) (B 64883 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R108019 : Reach 108019 := (sr 1 108019 162029 (by norm_num) (by norm_num) (sr 3 162029 60761 (by norm_num) (by norm_num) (B 60761 (by norm_num) (by norm_num) (by norm_num))))
theorem R108023 : Reach 108023 := (sr 1 108023 162035 (by norm_num) (by norm_num) (sr 1 162035 243053 (by norm_num) (by norm_num) (sr 3 243053 91145 (by norm_num) (by norm_num) (B 91145 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108027 : Reach 108027 := (sr 1 108027 162041 (by norm_num) (by norm_num) (sr 2 162041 121531 (by norm_num) (by norm_num) (sr 1 121531 182297 (by norm_num) (by norm_num) (sr 2 182297 136723 (by norm_num) (by norm_num) (sr 1 136723 205085 (by norm_num) (by norm_num) (sr 3 205085 76907 (by norm_num) (by norm_num) (B 76907 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108031 : Reach 108031 := (sr 1 108031 162047 (by norm_num) (by norm_num) (sr 1 162047 243071 (by norm_num) (by norm_num) (sr 1 243071 364607 (by norm_num) (by norm_num) (sr 1 364607 546911 (by norm_num) (by norm_num) (sr 1 546911 820367 (by norm_num) (by norm_num) (sr 1 820367 1230551 (by norm_num) (by norm_num) (sr 1 1230551 1845827 (by norm_num) (by norm_num) (sr 1 1845827 2768741 (by norm_num) (by norm_num) (sr 4 2768741 519139 (by norm_num) (by norm_num) (sr 1 519139 778709 (by norm_num) (by norm_num) (sr 7 778709 18251 (by norm_num) (by norm_num) (B 18251 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R108035 : Reach 108035 := (sr 1 108035 162053 (by norm_num) (by norm_num) (sr 4 162053 30385 (by norm_num) (by norm_num) (B 30385 (by norm_num) (by norm_num) (by norm_num))))
theorem R108039 : Reach 108039 := (sr 1 108039 162059 (by norm_num) (by norm_num) (sr 1 162059 243089 (by norm_num) (by norm_num) (sr 2 243089 182317 (by norm_num) (by norm_num) (sr 3 182317 68369 (by norm_num) (by norm_num) (B 68369 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108043 : Reach 108043 := (sr 1 108043 162065 (by norm_num) (by norm_num) (sr 2 162065 121549 (by norm_num) (by norm_num) (sr 3 121549 45581 (by norm_num) (by norm_num) (B 45581 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108047 : Reach 108047 := (sr 1 108047 162071 (by norm_num) (by norm_num) (sr 1 162071 243107 (by norm_num) (by norm_num) (sr 1 243107 364661 (by norm_num) (by norm_num) (sr 5 364661 34187 (by norm_num) (by norm_num) (B 34187 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108051 : Reach 108051 := (sr 1 108051 162077 (by norm_num) (by norm_num) (sr 3 162077 60779 (by norm_num) (by norm_num) (B 60779 (by norm_num) (by norm_num) (by norm_num))))
theorem R108055 : Reach 108055 := (sr 1 108055 162083 (by norm_num) (by norm_num) (sr 1 162083 243125 (by norm_num) (by norm_num) (sr 5 243125 22793 (by norm_num) (by norm_num) (B 22793 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108059 : Reach 108059 := (sr 1 108059 162089 (by norm_num) (by norm_num) (sr 2 162089 121567 (by norm_num) (by norm_num) (sr 1 121567 182351 (by norm_num) (by norm_num) (sr 1 182351 273527 (by norm_num) (by norm_num) (sr 1 273527 410291 (by norm_num) (by norm_num) (sr 1 410291 615437 (by norm_num) (by norm_num) (sr 3 615437 230789 (by norm_num) (by norm_num) (sr 4 230789 43273 (by norm_num) (by norm_num) (B 43273 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R108063 : Reach 108063 := (sr 1 108063 162095 (by norm_num) (by norm_num) (sr 1 162095 243143 (by norm_num) (by norm_num) (sr 1 243143 364715 (by norm_num) (by norm_num) (sr 1 364715 547073 (by norm_num) (by norm_num) (sr 2 547073 410305 (by norm_num) (by norm_num) (sr 2 410305 307729 (by norm_num) (by norm_num) (sr 2 307729 230797 (by norm_num) (by norm_num) (sr 3 230797 86549 (by norm_num) (by norm_num) (B 86549 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R108067 : Reach 108067 := (sr 1 108067 162101 (by norm_num) (by norm_num) (sr 5 162101 15197 (by norm_num) (by norm_num) (B 15197 (by norm_num) (by norm_num) (by norm_num))))
theorem R108071 : Reach 108071 := (sr 1 108071 162107 (by norm_num) (by norm_num) (sr 1 162107 243161 (by norm_num) (by norm_num) (sr 2 243161 182371 (by norm_num) (by norm_num) (sr 1 182371 273557 (by norm_num) (by norm_num) (sr 6 273557 12823 (by norm_num) (by norm_num) (B 12823 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R108075 : Reach 108075 := (sr 1 108075 162113 (by norm_num) (by norm_num) (sr 2 162113 121585 (by norm_num) (by norm_num) (sr 2 121585 91189 (by norm_num) (by norm_num) (B 91189 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108079 : Reach 108079 := (sr 1 108079 162119 (by norm_num) (by norm_num) (sr 1 162119 243179 (by norm_num) (by norm_num) (sr 1 243179 364769 (by norm_num) (by norm_num) (sr 2 364769 273577 (by norm_num) (by norm_num) (sr 2 273577 205183 (by norm_num) (by norm_num) (sr 1 205183 307775 (by norm_num) (by norm_num) (sr 1 307775 461663 (by norm_num) (by norm_num) (sr 1 461663 692495 (by norm_num) (by norm_num) (sr 1 692495 1038743 (by norm_num) (by norm_num) (sr 1 1038743 1558115 (by norm_num) (by norm_num) (sr 1 1558115 2337173 (by norm_num) (by norm_num) (sr 6 2337173 109555 (by norm_num) (by norm_num) (sr 1 109555 164333 (by norm_num) (by norm_num) (sr 3 164333 61625 (by norm_num) (by norm_num) (B 61625 (by norm_num) (by norm_num) (by norm_num))))))))))))))))
theorem R108083 : Reach 108083 := (sr 1 108083 162125 (by norm_num) (by norm_num) (sr 3 162125 60797 (by norm_num) (by norm_num) (B 60797 (by norm_num) (by norm_num) (by norm_num))))
theorem R108087 : Reach 108087 := (sr 1 108087 162131 (by norm_num) (by norm_num) (sr 1 162131 243197 (by norm_num) (by norm_num) (sr 3 243197 91199 (by norm_num) (by norm_num) (B 91199 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108091 : Reach 108091 := (sr 1 108091 162137 (by norm_num) (by norm_num) (sr 2 162137 121603 (by norm_num) (by norm_num) (sr 1 121603 182405 (by norm_num) (by norm_num) (sr 4 182405 34201 (by norm_num) (by norm_num) (B 34201 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108095 : Reach 108095 := (sr 1 108095 162143 (by norm_num) (by norm_num) (sr 1 162143 243215 (by norm_num) (by norm_num) (sr 1 243215 364823 (by norm_num) (by norm_num) (sr 1 364823 547235 (by norm_num) (by norm_num) (sr 1 547235 820853 (by norm_num) (by norm_num) (sr 5 820853 76955 (by norm_num) (by norm_num) (B 76955 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108099 : Reach 108099 := (sr 1 108099 162149 (by norm_num) (by norm_num) (sr 4 162149 30403 (by norm_num) (by norm_num) (B 30403 (by norm_num) (by norm_num) (by norm_num))))
theorem R108103 : Reach 108103 := (sr 1 108103 162155 (by norm_num) (by norm_num) (sr 1 162155 243233 (by norm_num) (by norm_num) (sr 2 243233 182425 (by norm_num) (by norm_num) (sr 2 182425 136819 (by norm_num) (by norm_num) (sr 1 136819 205229 (by norm_num) (by norm_num) (sr 3 205229 76961 (by norm_num) (by norm_num) (B 76961 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108107 : Reach 108107 := (sr 1 108107 162161 (by norm_num) (by norm_num) (sr 2 162161 121621 (by norm_num) (by norm_num) (sr 6 121621 5701 (by norm_num) (by norm_num) (B 5701 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108111 : Reach 108111 := (sr 1 108111 162167 (by norm_num) (by norm_num) (sr 1 162167 243251 (by norm_num) (by norm_num) (sr 1 243251 364877 (by norm_num) (by norm_num) (sr 3 364877 136829 (by norm_num) (by norm_num) (sr 3 136829 51311 (by norm_num) (by norm_num) (B 51311 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R108115 : Reach 108115 := (sr 1 108115 162173 (by norm_num) (by norm_num) (sr 3 162173 60815 (by norm_num) (by norm_num) (B 60815 (by norm_num) (by norm_num) (by norm_num))))
theorem R108119 : Reach 108119 := (sr 1 108119 162179 (by norm_num) (by norm_num) (sr 1 162179 243269 (by norm_num) (by norm_num) (sr 4 243269 45613 (by norm_num) (by norm_num) (B 45613 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108123 : Reach 108123 := (sr 1 108123 162185 (by norm_num) (by norm_num) (sr 2 162185 121639 (by norm_num) (by norm_num) (sr 1 121639 182459 (by norm_num) (by norm_num) (sr 1 182459 273689 (by norm_num) (by norm_num) (sr 2 273689 205267 (by norm_num) (by norm_num) (sr 1 205267 307901 (by norm_num) (by norm_num) (sr 3 307901 115463 (by norm_num) (by norm_num) (sr 1 115463 173195 (by norm_num) (by norm_num) (sr 1 173195 259793 (by norm_num) (by norm_num) (sr 2 259793 194845 (by norm_num) (by norm_num) (sr 3 194845 73067 (by norm_num) (by norm_num) (B 73067 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R108127 : Reach 108127 := (sr 1 108127 162191 (by norm_num) (by norm_num) (sr 1 162191 243287 (by norm_num) (by norm_num) (sr 1 243287 364931 (by norm_num) (by norm_num) (sr 1 364931 547397 (by norm_num) (by norm_num) (sr 4 547397 102637 (by norm_num) (by norm_num) (sr 3 102637 38489 (by norm_num) (by norm_num) (B 38489 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108131 : Reach 108131 := (sr 1 108131 162197 (by norm_num) (by norm_num) (sr 6 162197 7603 (by norm_num) (by norm_num) (B 7603 (by norm_num) (by norm_num) (by norm_num))))
theorem R108135 : Reach 108135 := (sr 1 108135 162203 (by norm_num) (by norm_num) (sr 1 162203 243305 (by norm_num) (by norm_num) (sr 2 243305 182479 (by norm_num) (by norm_num) (sr 1 182479 273719 (by norm_num) (by norm_num) (sr 1 273719 410579 (by norm_num) (by norm_num) (sr 1 410579 615869 (by norm_num) (by norm_num) (sr 3 615869 230951 (by norm_num) (by norm_num) (sr 1 230951 346427 (by norm_num) (by norm_num) (sr 1 346427 519641 (by norm_num) (by norm_num) (sr 2 519641 389731 (by norm_num) (by norm_num) (sr 1 389731 584597 (by norm_num) (by norm_num) (sr 6 584597 27403 (by norm_num) (by norm_num) (B 27403 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R108139 : Reach 108139 := (sr 1 108139 162209 (by norm_num) (by norm_num) (sr 2 162209 121657 (by norm_num) (by norm_num) (sr 2 121657 91243 (by norm_num) (by norm_num) (B 91243 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108143 : Reach 108143 := (sr 1 108143 162215 (by norm_num) (by norm_num) (sr 1 162215 243323 (by norm_num) (by norm_num) (sr 1 243323 364985 (by norm_num) (by norm_num) (sr 2 364985 273739 (by norm_num) (by norm_num) (sr 1 273739 410609 (by norm_num) (by norm_num) (sr 2 410609 307957 (by norm_num) (by norm_num) (sr 5 307957 28871 (by norm_num) (by norm_num) (B 28871 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R108147 : Reach 108147 := (sr 1 108147 162221 (by norm_num) (by norm_num) (sr 3 162221 60833 (by norm_num) (by norm_num) (B 60833 (by norm_num) (by norm_num) (by norm_num))))
theorem R108151 : Reach 108151 := (sr 1 108151 162227 (by norm_num) (by norm_num) (sr 1 162227 243341 (by norm_num) (by norm_num) (sr 3 243341 91253 (by norm_num) (by norm_num) (B 91253 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108155 : Reach 108155 := (sr 1 108155 162233 (by norm_num) (by norm_num) (sr 2 162233 121675 (by norm_num) (by norm_num) (sr 1 121675 182513 (by norm_num) (by norm_num) (sr 2 182513 136885 (by norm_num) (by norm_num) (sr 5 136885 12833 (by norm_num) (by norm_num) (B 12833 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R108159 : Reach 108159 := (sr 1 108159 162239 (by norm_num) (by norm_num) (sr 1 162239 243359 (by norm_num) (by norm_num) (sr 1 243359 365039 (by norm_num) (by norm_num) (sr 1 365039 547559 (by norm_num) (by norm_num) (sr 1 547559 821339 (by norm_num) (by norm_num) (sr 1 821339 1232009 (by norm_num) (by norm_num) (sr 2 1232009 924007 (by norm_num) (by norm_num) (sr 1 924007 1386011 (by norm_num) (by norm_num) (sr 1 1386011 2079017 (by norm_num) (by norm_num) (sr 2 2079017 1559263 (by norm_num) (by norm_num) (sr 1 1559263 2338895 (by norm_num) (by norm_num) (sr 1 2338895 3508343 (by norm_num) (by norm_num) (sr 1 3508343 5262515 (by norm_num) (by norm_num) (sr 1 5262515 7893773 (by norm_num) (by norm_num) (sr 3 7893773 2960165 (by norm_num) (by norm_num) (sr 4 2960165 555031 (by norm_num) (by norm_num) (sr 1 555031 832547 (by norm_num) (by norm_num) (sr 1 832547 1248821 (by norm_num) (by norm_num) (sr 5 1248821 117077 (by norm_num) (by norm_num) (sr 10 117077 343 (by norm_num) (by norm_num) (B 343 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))
theorem R108163 : Reach 108163 := (sr 1 108163 162245 (by norm_num) (by norm_num) (sr 4 162245 30421 (by norm_num) (by norm_num) (B 30421 (by norm_num) (by norm_num) (by norm_num))))
theorem R108167 : Reach 108167 := (sr 1 108167 162251 (by norm_num) (by norm_num) (sr 1 162251 243377 (by norm_num) (by norm_num) (sr 2 243377 182533 (by norm_num) (by norm_num) (sr 4 182533 34225 (by norm_num) (by norm_num) (B 34225 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108171 : Reach 108171 := (sr 1 108171 162257 (by norm_num) (by norm_num) (sr 2 162257 121693 (by norm_num) (by norm_num) (sr 3 121693 45635 (by norm_num) (by norm_num) (B 45635 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108175 : Reach 108175 := (sr 1 108175 162263 (by norm_num) (by norm_num) (sr 1 162263 243395 (by norm_num) (by norm_num) (sr 1 243395 365093 (by norm_num) (by norm_num) (sr 4 365093 68455 (by norm_num) (by norm_num) (B 68455 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108179 : Reach 108179 := (sr 1 108179 162269 (by norm_num) (by norm_num) (sr 3 162269 60851 (by norm_num) (by norm_num) (B 60851 (by norm_num) (by norm_num) (by norm_num))))
theorem R108183 : Reach 108183 := (sr 1 108183 162275 (by norm_num) (by norm_num) (sr 1 162275 243413 (by norm_num) (by norm_num) (sr 7 243413 5705 (by norm_num) (by norm_num) (B 5705 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108187 : Reach 108187 := (sr 1 108187 162281 (by norm_num) (by norm_num) (sr 2 162281 121711 (by norm_num) (by norm_num) (sr 1 121711 182567 (by norm_num) (by norm_num) (sr 1 182567 273851 (by norm_num) (by norm_num) (sr 1 273851 410777 (by norm_num) (by norm_num) (sr 2 410777 308083 (by norm_num) (by norm_num) (sr 1 308083 462125 (by norm_num) (by norm_num) (sr 3 462125 173297 (by norm_num) (by norm_num) (sr 2 173297 129973 (by norm_num) (by norm_num) (sr 5 129973 12185 (by norm_num) (by norm_num) (B 12185 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R108191 : Reach 108191 := (sr 1 108191 162287 (by norm_num) (by norm_num) (sr 1 162287 243431 (by norm_num) (by norm_num) (sr 1 243431 365147 (by norm_num) (by norm_num) (sr 1 365147 547721 (by norm_num) (by norm_num) (sr 2 547721 410791 (by norm_num) (by norm_num) (sr 1 410791 616187 (by norm_num) (by norm_num) (sr 1 616187 924281 (by norm_num) (by norm_num) (sr 2 924281 693211 (by norm_num) (by norm_num) (sr 1 693211 1039817 (by norm_num) (by norm_num) (sr 2 1039817 779863 (by norm_num) (by norm_num) (sr 1 779863 1169795 (by norm_num) (by norm_num) (sr 1 1169795 1754693 (by norm_num) (by norm_num) (sr 4 1754693 329005 (by norm_num) (by norm_num) (sr 3 329005 123377 (by norm_num) (by norm_num) (sr 2 123377 92533 (by norm_num) (by norm_num) (B 92533 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R108195 : Reach 108195 := (sr 1 108195 162293 (by norm_num) (by norm_num) (sr 5 162293 15215 (by norm_num) (by norm_num) (B 15215 (by norm_num) (by norm_num) (by norm_num))))
theorem R108199 : Reach 108199 := (sr 1 108199 162299 (by norm_num) (by norm_num) (sr 1 162299 243449 (by norm_num) (by norm_num) (sr 2 243449 182587 (by norm_num) (by norm_num) (sr 1 182587 273881 (by norm_num) (by norm_num) (sr 2 273881 205411 (by norm_num) (by norm_num) (sr 1 205411 308117 (by norm_num) (by norm_num) (sr 6 308117 14443 (by norm_num) (by norm_num) (B 14443 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R108203 : Reach 108203 := (sr 1 108203 162305 (by norm_num) (by norm_num) (sr 2 162305 121729 (by norm_num) (by norm_num) (sr 2 121729 91297 (by norm_num) (by norm_num) (B 91297 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108207 : Reach 108207 := (sr 1 108207 162311 (by norm_num) (by norm_num) (sr 1 162311 243467 (by norm_num) (by norm_num) (sr 1 243467 365201 (by norm_num) (by norm_num) (sr 2 365201 273901 (by norm_num) (by norm_num) (sr 3 273901 102713 (by norm_num) (by norm_num) (sr 2 102713 77035 (by norm_num) (by norm_num) (B 77035 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108211 : Reach 108211 := (sr 1 108211 162317 (by norm_num) (by norm_num) (sr 3 162317 60869 (by norm_num) (by norm_num) (B 60869 (by norm_num) (by norm_num) (by norm_num))))
theorem R108215 : Reach 108215 := (sr 1 108215 162323 (by norm_num) (by norm_num) (sr 1 162323 243485 (by norm_num) (by norm_num) (sr 3 243485 91307 (by norm_num) (by norm_num) (B 91307 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108219 : Reach 108219 := (sr 1 108219 162329 (by norm_num) (by norm_num) (sr 2 162329 121747 (by norm_num) (by norm_num) (sr 1 121747 182621 (by norm_num) (by norm_num) (sr 3 182621 68483 (by norm_num) (by norm_num) (B 68483 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108223 : Reach 108223 := (sr 1 108223 162335 (by norm_num) (by norm_num) (sr 1 162335 243503 (by norm_num) (by norm_num) (sr 1 243503 365255 (by norm_num) (by norm_num) (sr 1 365255 547883 (by norm_num) (by norm_num) (sr 1 547883 821825 (by norm_num) (by norm_num) (sr 2 821825 616369 (by norm_num) (by norm_num) (sr 2 616369 462277 (by norm_num) (by norm_num) (sr 4 462277 86677 (by norm_num) (by norm_num) (B 86677 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R108227 : Reach 108227 := (sr 1 108227 162341 (by norm_num) (by norm_num) (sr 4 162341 30439 (by norm_num) (by norm_num) (B 30439 (by norm_num) (by norm_num) (by norm_num))))
theorem R108231 : Reach 108231 := (sr 1 108231 162347 (by norm_num) (by norm_num) (sr 1 162347 243521 (by norm_num) (by norm_num) (sr 2 243521 182641 (by norm_num) (by norm_num) (sr 2 182641 136981 (by norm_num) (by norm_num) (sr 6 136981 6421 (by norm_num) (by norm_num) (B 6421 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R108235 : Reach 108235 := (sr 1 108235 162353 (by norm_num) (by norm_num) (sr 2 162353 121765 (by norm_num) (by norm_num) (sr 4 121765 22831 (by norm_num) (by norm_num) (B 22831 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108239 : Reach 108239 := (sr 1 108239 162359 (by norm_num) (by norm_num) (sr 1 162359 243539 (by norm_num) (by norm_num) (sr 1 243539 365309 (by norm_num) (by norm_num) (sr 3 365309 136991 (by norm_num) (by norm_num) (sr 1 136991 205487 (by norm_num) (by norm_num) (sr 1 205487 308231 (by norm_num) (by norm_num) (sr 1 308231 462347 (by norm_num) (by norm_num) (sr 1 462347 693521 (by norm_num) (by norm_num) (sr 2 693521 520141 (by norm_num) (by norm_num) (sr 3 520141 195053 (by norm_num) (by norm_num) (sr 3 195053 73145 (by norm_num) (by norm_num) (B 73145 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R108243 : Reach 108243 := (sr 1 108243 162365 (by norm_num) (by norm_num) (sr 3 162365 60887 (by norm_num) (by norm_num) (B 60887 (by norm_num) (by norm_num) (by norm_num))))
theorem R108247 : Reach 108247 := (sr 1 108247 162371 (by norm_num) (by norm_num) (sr 1 162371 243557 (by norm_num) (by norm_num) (sr 4 243557 45667 (by norm_num) (by norm_num) (B 45667 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108251 : Reach 108251 := (sr 1 108251 162377 (by norm_num) (by norm_num) (sr 2 162377 121783 (by norm_num) (by norm_num) (sr 1 121783 182675 (by norm_num) (by norm_num) (sr 1 182675 274013 (by norm_num) (by norm_num) (sr 3 274013 102755 (by norm_num) (by norm_num) R102755)))))
theorem R108255 : Reach 108255 := (sr 1 108255 162383 (by norm_num) (by norm_num) (sr 1 162383 243575 (by norm_num) (by norm_num) (sr 1 243575 365363 (by norm_num) (by norm_num) (sr 1 365363 548045 (by norm_num) (by norm_num) (sr 3 548045 205517 (by norm_num) (by norm_num) (sr 3 205517 77069 (by norm_num) (by norm_num) (B 77069 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108259 : Reach 108259 := (sr 1 108259 162389 (by norm_num) (by norm_num) (sr 8 162389 1903 (by norm_num) (by norm_num) (B 1903 (by norm_num) (by norm_num) (by norm_num))))
theorem R108263 : Reach 108263 := (sr 1 108263 162395 (by norm_num) (by norm_num) (sr 1 162395 243593 (by norm_num) (by norm_num) (sr 2 243593 182695 (by norm_num) (by norm_num) (sr 1 182695 274043 (by norm_num) (by norm_num) (sr 1 274043 411065 (by norm_num) (by norm_num) (sr 2 411065 308299 (by norm_num) (by norm_num) (sr 1 308299 462449 (by norm_num) (by norm_num) (sr 2 462449 346837 (by norm_num) (by norm_num) (sr 7 346837 8129 (by norm_num) (by norm_num) (B 8129 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R108267 : Reach 108267 := (sr 1 108267 162401 (by norm_num) (by norm_num) (sr 2 162401 121801 (by norm_num) (by norm_num) (sr 2 121801 91351 (by norm_num) (by norm_num) (B 91351 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108271 : Reach 108271 := (sr 1 108271 162407 (by norm_num) (by norm_num) (sr 1 162407 243611 (by norm_num) (by norm_num) (sr 1 243611 365417 (by norm_num) (by norm_num) (sr 2 365417 274063 (by norm_num) (by norm_num) (sr 1 274063 411095 (by norm_num) (by norm_num) (sr 1 411095 616643 (by norm_num) (by norm_num) (sr 1 616643 924965 (by norm_num) (by norm_num) (sr 4 924965 173431 (by norm_num) (by norm_num) (sr 1 173431 260147 (by norm_num) (by norm_num) (sr 1 260147 390221 (by norm_num) (by norm_num) (sr 3 390221 146333 (by norm_num) (by norm_num) (sr 3 146333 54875 (by norm_num) (by norm_num) (B 54875 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R108275 : Reach 108275 := (sr 1 108275 162413 (by norm_num) (by norm_num) (sr 3 162413 60905 (by norm_num) (by norm_num) (B 60905 (by norm_num) (by norm_num) (by norm_num))))
theorem R108279 : Reach 108279 := (sr 1 108279 162419 (by norm_num) (by norm_num) (sr 1 162419 243629 (by norm_num) (by norm_num) (sr 3 243629 91361 (by norm_num) (by norm_num) (B 91361 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108283 : Reach 108283 := (sr 1 108283 162425 (by norm_num) (by norm_num) (sr 2 162425 121819 (by norm_num) (by norm_num) (sr 1 121819 182729 (by norm_num) (by norm_num) (sr 2 182729 137047 (by norm_num) (by norm_num) (sr 1 137047 205571 (by norm_num) (by norm_num) (sr 1 205571 308357 (by norm_num) (by norm_num) (sr 4 308357 57817 (by norm_num) (by norm_num) (B 57817 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R108287 : Reach 108287 := (sr 1 108287 162431 (by norm_num) (by norm_num) (sr 1 162431 243647 (by norm_num) (by norm_num) (sr 1 243647 365471 (by norm_num) (by norm_num) (sr 1 365471 548207 (by norm_num) (by norm_num) (sr 1 548207 822311 (by norm_num) (by norm_num) (sr 1 822311 1233467 (by norm_num) (by norm_num) (sr 1 1233467 1850201 (by norm_num) (by norm_num) (sr 2 1850201 1387651 (by norm_num) (by norm_num) (sr 1 1387651 2081477 (by norm_num) (by norm_num) (sr 4 2081477 390277 (by norm_num) (by norm_num) (sr 4 390277 73177 (by norm_num) (by norm_num) (B 73177 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R108291 : Reach 108291 := (sr 1 108291 162437 (by norm_num) (by norm_num) (sr 4 162437 30457 (by norm_num) (by norm_num) (B 30457 (by norm_num) (by norm_num) (by norm_num))))
theorem R108295 : Reach 108295 := (sr 1 108295 162443 (by norm_num) (by norm_num) (sr 1 162443 243665 (by norm_num) (by norm_num) (sr 2 243665 182749 (by norm_num) (by norm_num) (sr 3 182749 68531 (by norm_num) (by norm_num) (B 68531 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108299 : Reach 108299 := (sr 1 108299 162449 (by norm_num) (by norm_num) (sr 2 162449 121837 (by norm_num) (by norm_num) (sr 3 121837 45689 (by norm_num) (by norm_num) (B 45689 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108303 : Reach 108303 := (sr 1 108303 162455 (by norm_num) (by norm_num) (sr 1 162455 243683 (by norm_num) (by norm_num) (sr 1 243683 365525 (by norm_num) (by norm_num) (sr 7 365525 8567 (by norm_num) (by norm_num) (B 8567 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108307 : Reach 108307 := (sr 1 108307 162461 (by norm_num) (by norm_num) (sr 3 162461 60923 (by norm_num) (by norm_num) (B 60923 (by norm_num) (by norm_num) (by norm_num))))
theorem R108311 : Reach 108311 := (sr 1 108311 162467 (by norm_num) (by norm_num) (sr 1 162467 243701 (by norm_num) (by norm_num) (sr 5 243701 22847 (by norm_num) (by norm_num) (B 22847 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108315 : Reach 108315 := (sr 1 108315 162473 (by norm_num) (by norm_num) (sr 2 162473 121855 (by norm_num) (by norm_num) (sr 1 121855 182783 (by norm_num) (by norm_num) (sr 1 182783 274175 (by norm_num) (by norm_num) (sr 1 274175 411263 (by norm_num) (by norm_num) (sr 1 411263 616895 (by norm_num) (by norm_num) (sr 1 616895 925343 (by norm_num) (by norm_num) (sr 1 925343 1388015 (by norm_num) (by norm_num) (sr 1 1388015 2082023 (by norm_num) (by norm_num) (sr 1 2082023 3123035 (by norm_num) (by norm_num) (sr 1 3123035 4684553 (by norm_num) (by norm_num) (sr 2 4684553 3513415 (by norm_num) (by norm_num) (sr 1 3513415 5270123 (by norm_num) (by norm_num) (sr 1 5270123 7905185 (by norm_num) (by norm_num) (sr 2 7905185 5928889 (by norm_num) (by norm_num) (sr 2 5928889 4446667 (by norm_num) (by norm_num) (sr 1 4446667 6670001 (by norm_num) (by norm_num) (sr 2 6670001 5002501 (by norm_num) (by norm_num) (sr 4 5002501 937969 (by norm_num) (by norm_num) (sr 2 937969 703477 (by norm_num) (by norm_num) (sr 5 703477 65951 (by norm_num) (by norm_num) (B 65951 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))
theorem R108319 : Reach 108319 := (sr 1 108319 162479 (by norm_num) (by norm_num) (sr 1 162479 243719 (by norm_num) (by norm_num) (sr 1 243719 365579 (by norm_num) (by norm_num) (sr 1 365579 548369 (by norm_num) (by norm_num) (sr 2 548369 411277 (by norm_num) (by norm_num) (sr 3 411277 154229 (by norm_num) (by norm_num) (sr 5 154229 14459 (by norm_num) (by norm_num) (B 14459 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R108323 : Reach 108323 := (sr 1 108323 162485 (by norm_num) (by norm_num) (sr 5 162485 15233 (by norm_num) (by norm_num) (B 15233 (by norm_num) (by norm_num) (by norm_num))))
theorem R108327 : Reach 108327 := (sr 1 108327 162491 (by norm_num) (by norm_num) (sr 1 162491 243737 (by norm_num) (by norm_num) (sr 2 243737 182803 (by norm_num) (by norm_num) (sr 1 182803 274205 (by norm_num) (by norm_num) (sr 3 274205 102827 (by norm_num) (by norm_num) R102827)))))
theorem R108331 : Reach 108331 := (sr 1 108331 162497 (by norm_num) (by norm_num) (sr 2 162497 121873 (by norm_num) (by norm_num) (sr 2 121873 91405 (by norm_num) (by norm_num) (B 91405 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108335 : Reach 108335 := (sr 1 108335 162503 (by norm_num) (by norm_num) (sr 1 162503 243755 (by norm_num) (by norm_num) (sr 1 243755 365633 (by norm_num) (by norm_num) (sr 2 365633 274225 (by norm_num) (by norm_num) (sr 2 274225 205669 (by norm_num) (by norm_num) (sr 4 205669 38563 (by norm_num) (by norm_num) (B 38563 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108339 : Reach 108339 := (sr 1 108339 162509 (by norm_num) (by norm_num) (sr 3 162509 60941 (by norm_num) (by norm_num) (B 60941 (by norm_num) (by norm_num) (by norm_num))))
theorem R108343 : Reach 108343 := (sr 1 108343 162515 (by norm_num) (by norm_num) (sr 1 162515 243773 (by norm_num) (by norm_num) (sr 3 243773 91415 (by norm_num) (by norm_num) (B 91415 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108347 : Reach 108347 := (sr 1 108347 162521 (by norm_num) (by norm_num) (sr 2 162521 121891 (by norm_num) (by norm_num) (sr 1 121891 182837 (by norm_num) (by norm_num) (sr 5 182837 17141 (by norm_num) (by norm_num) (B 17141 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108351 : Reach 108351 := (sr 1 108351 162527 (by norm_num) (by norm_num) (sr 1 162527 243791 (by norm_num) (by norm_num) (sr 1 243791 365687 (by norm_num) (by norm_num) (sr 1 365687 548531 (by norm_num) (by norm_num) (sr 1 548531 822797 (by norm_num) (by norm_num) (sr 3 822797 308549 (by norm_num) (by norm_num) (sr 4 308549 57853 (by norm_num) (by norm_num) (B 57853 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R108355 : Reach 108355 := (sr 1 108355 162533 (by norm_num) (by norm_num) (sr 4 162533 30475 (by norm_num) (by norm_num) (B 30475 (by norm_num) (by norm_num) (by norm_num))))
theorem R108359 : Reach 108359 := (sr 1 108359 162539 (by norm_num) (by norm_num) (sr 1 162539 243809 (by norm_num) (by norm_num) (sr 2 243809 182857 (by norm_num) (by norm_num) (sr 2 182857 137143 (by norm_num) (by norm_num) (sr 1 137143 205715 (by norm_num) (by norm_num) (sr 1 205715 308573 (by norm_num) (by norm_num) (sr 3 308573 115715 (by norm_num) (by norm_num) (sr 1 115715 173573 (by norm_num) (by norm_num) (sr 4 173573 32545 (by norm_num) (by norm_num) (B 32545 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R108363 : Reach 108363 := (sr 1 108363 162545 (by norm_num) (by norm_num) (sr 2 162545 121909 (by norm_num) (by norm_num) (sr 5 121909 11429 (by norm_num) (by norm_num) (B 11429 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108367 : Reach 108367 := (sr 1 108367 162551 (by norm_num) (by norm_num) (sr 1 162551 243827 (by norm_num) (by norm_num) (sr 1 243827 365741 (by norm_num) (by norm_num) (sr 3 365741 137153 (by norm_num) (by norm_num) (sr 2 137153 102865 (by norm_num) (by norm_num) (sr 2 102865 77149 (by norm_num) (by norm_num) (B 77149 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108371 : Reach 108371 := (sr 1 108371 162557 (by norm_num) (by norm_num) (sr 3 162557 60959 (by norm_num) (by norm_num) (B 60959 (by norm_num) (by norm_num) (by norm_num))))
theorem R108375 : Reach 108375 := (sr 1 108375 162563 (by norm_num) (by norm_num) (sr 1 162563 243845 (by norm_num) (by norm_num) (sr 4 243845 45721 (by norm_num) (by norm_num) (B 45721 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108379 : Reach 108379 := (sr 1 108379 162569 (by norm_num) (by norm_num) (sr 2 162569 121927 (by norm_num) (by norm_num) (sr 1 121927 182891 (by norm_num) (by norm_num) (sr 1 182891 274337 (by norm_num) (by norm_num) (sr 2 274337 205753 (by norm_num) (by norm_num) (sr 2 205753 154315 (by norm_num) (by norm_num) (sr 1 154315 231473 (by norm_num) (by norm_num) (sr 2 231473 173605 (by norm_num) (by norm_num) (sr 4 173605 32551 (by norm_num) (by norm_num) (B 32551 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R108383 : Reach 108383 := (sr 1 108383 162575 (by norm_num) (by norm_num) (sr 1 162575 243863 (by norm_num) (by norm_num) (sr 1 243863 365795 (by norm_num) (by norm_num) (sr 1 365795 548693 (by norm_num) (by norm_num) (sr 9 548693 3215 (by norm_num) (by norm_num) (B 3215 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R108387 : Reach 108387 := (sr 1 108387 162581 (by norm_num) (by norm_num) (sr 6 162581 7621 (by norm_num) (by norm_num) (B 7621 (by norm_num) (by norm_num) (by norm_num))))
theorem R108391 : Reach 108391 := (sr 1 108391 162587 (by norm_num) (by norm_num) (sr 1 162587 243881 (by norm_num) (by norm_num) (sr 2 243881 182911 (by norm_num) (by norm_num) (sr 1 182911 274367 (by norm_num) (by norm_num) (sr 1 274367 411551 (by norm_num) (by norm_num) (sr 1 411551 617327 (by norm_num) (by norm_num) (sr 1 617327 925991 (by norm_num) (by norm_num) (sr 1 925991 1388987 (by norm_num) (by norm_num) (sr 1 1388987 2083481 (by norm_num) (by norm_num) (sr 2 2083481 1562611 (by norm_num) (by norm_num) (sr 1 1562611 2343917 (by norm_num) (by norm_num) (sr 3 2343917 878969 (by norm_num) (by norm_num) (sr 2 878969 659227 (by norm_num) (by norm_num) (sr 1 659227 988841 (by norm_num) (by norm_num) (sr 2 988841 741631 (by norm_num) (by norm_num) (sr 1 741631 1112447 (by norm_num) (by norm_num) (sr 1 1112447 1668671 (by norm_num) (by norm_num) (sr 1 1668671 2503007 (by norm_num) (by norm_num) (sr 1 2503007 3754511 (by norm_num) (by norm_num) (sr 1 3754511 5631767 (by norm_num) (by norm_num) (sr 1 5631767 8447651 (by norm_num) (by norm_num) (sr 1 8447651 12671477 (by norm_num) (by norm_num) (sr 5 12671477 1187951 (by norm_num) (by norm_num) (sr 1 1187951 1781927 (by norm_num) (by norm_num) (sr 1 1781927 2672891 (by norm_num) (by norm_num) (sr 1 2672891 4009337 (by norm_num) (by norm_num) (sr 2 4009337 3007003 (by norm_num) (by norm_num) (sr 1 3007003 4510505 (by norm_num) (by norm_num) (sr 2 4510505 3382879 (by norm_num) (by norm_num) (sr 1 3382879 5074319 (by norm_num) (by norm_num) (sr 1 5074319 7611479 (by norm_num) (by norm_num) (sr 1 7611479 11417219 (by norm_num) (by norm_num) (sr 1 11417219 17125829 (by norm_num) (by norm_num) (sr 4 17125829 3211093 (by norm_num) (by norm_num) (sr 9 3211093 18815 (by norm_num) (by norm_num) (B 18815 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))))))))
theorem R108395 : Reach 108395 := (sr 1 108395 162593 (by norm_num) (by norm_num) (sr 2 162593 121945 (by norm_num) (by norm_num) (sr 2 121945 91459 (by norm_num) (by norm_num) (B 91459 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108399 : Reach 108399 := (sr 1 108399 162599 (by norm_num) (by norm_num) (sr 1 162599 243899 (by norm_num) (by norm_num) (sr 1 243899 365849 (by norm_num) (by norm_num) (sr 2 365849 274387 (by norm_num) (by norm_num) (sr 1 274387 411581 (by norm_num) (by norm_num) (sr 3 411581 154343 (by norm_num) (by norm_num) (sr 1 154343 231515 (by norm_num) (by norm_num) (sr 1 231515 347273 (by norm_num) (by norm_num) (sr 2 347273 260455 (by norm_num) (by norm_num) (sr 1 260455 390683 (by norm_num) (by norm_num) (sr 1 390683 586025 (by norm_num) (by norm_num) (sr 2 586025 439519 (by norm_num) (by norm_num) (sr 1 439519 659279 (by norm_num) (by norm_num) (sr 1 659279 988919 (by norm_num) (by norm_num) (sr 1 988919 1483379 (by norm_num) (by norm_num) (sr 1 1483379 2225069 (by norm_num) (by norm_num) (sr 3 2225069 834401 (by norm_num) (by norm_num) (sr 2 834401 625801 (by norm_num) (by norm_num) (sr 2 625801 469351 (by norm_num) (by norm_num) (sr 1 469351 704027 (by norm_num) (by norm_num) (sr 1 704027 1056041 (by norm_num) (by norm_num) (sr 2 1056041 792031 (by norm_num) (by norm_num) (sr 1 792031 1188047 (by norm_num) (by norm_num) (sr 1 1188047 1782071 (by norm_num) (by norm_num) (sr 1 1782071 2673107 (by norm_num) (by norm_num) (sr 1 2673107 4009661 (by norm_num) (by norm_num) (sr 3 4009661 1503623 (by norm_num) (by norm_num) (sr 1 1503623 2255435 (by norm_num) (by norm_num) (sr 1 2255435 3383153 (by norm_num) (by norm_num) (sr 2 3383153 2537365 (by norm_num) (by norm_num) (sr 6 2537365 118939 (by norm_num) (by norm_num) (sr 1 118939 178409 (by norm_num) (by norm_num) (sr 2 178409 133807 (by norm_num) (by norm_num) (sr 1 133807 200711 (by norm_num) (by norm_num) (sr 1 200711 301067 (by norm_num) (by norm_num) (sr 1 301067 451601 (by norm_num) (by norm_num) (sr 2 451601 338701 (by norm_num) (by norm_num) (sr 3 338701 127013 (by norm_num) (by norm_num) (sr 4 127013 23815 (by norm_num) (by norm_num) (B 23815 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))))))))))))
theorem R108403 : Reach 108403 := (sr 1 108403 162605 (by norm_num) (by norm_num) (sr 3 162605 60977 (by norm_num) (by norm_num) (B 60977 (by norm_num) (by norm_num) (by norm_num))))
theorem R108407 : Reach 108407 := (sr 1 108407 162611 (by norm_num) (by norm_num) (sr 1 162611 243917 (by norm_num) (by norm_num) (sr 3 243917 91469 (by norm_num) (by norm_num) (B 91469 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108411 : Reach 108411 := (sr 1 108411 162617 (by norm_num) (by norm_num) (sr 2 162617 121963 (by norm_num) (by norm_num) (sr 1 121963 182945 (by norm_num) (by norm_num) (sr 2 182945 137209 (by norm_num) (by norm_num) (sr 2 137209 102907 (by norm_num) (by norm_num) R102907)))))
theorem R108415 : Reach 108415 := (sr 1 108415 162623 (by norm_num) (by norm_num) (sr 1 162623 243935 (by norm_num) (by norm_num) (sr 1 243935 365903 (by norm_num) (by norm_num) (sr 1 365903 548855 (by norm_num) (by norm_num) (sr 1 548855 823283 (by norm_num) (by norm_num) (sr 1 823283 1234925 (by norm_num) (by norm_num) (sr 3 1234925 463097 (by norm_num) (by norm_num) (sr 2 463097 347323 (by norm_num) (by norm_num) (sr 1 347323 520985 (by norm_num) (by norm_num) (sr 2 520985 390739 (by norm_num) (by norm_num) (sr 1 390739 586109 (by norm_num) (by norm_num) (sr 3 586109 219791 (by norm_num) (by norm_num) (sr 1 219791 329687 (by norm_num) (by norm_num) (sr 1 329687 494531 (by norm_num) (by norm_num) (sr 1 494531 741797 (by norm_num) (by norm_num) (sr 4 741797 139087 (by norm_num) (by norm_num) (sr 1 139087 208631 (by norm_num) (by norm_num) (sr 1 208631 312947 (by norm_num) (by norm_num) (sr 1 312947 469421 (by norm_num) (by norm_num) (sr 3 469421 176033 (by norm_num) (by norm_num) (sr 2 176033 132025 (by norm_num) (by norm_num) (sr 2 132025 99019 (by norm_num) (by norm_num) (B 99019 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R108419 : Reach 108419 := (sr 1 108419 162629 (by norm_num) (by norm_num) (sr 4 162629 30493 (by norm_num) (by norm_num) (B 30493 (by norm_num) (by norm_num) (by norm_num))))
theorem R108423 : Reach 108423 := (sr 1 108423 162635 (by norm_num) (by norm_num) (sr 1 162635 243953 (by norm_num) (by norm_num) (sr 2 243953 182965 (by norm_num) (by norm_num) (sr 5 182965 17153 (by norm_num) (by norm_num) (B 17153 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108427 : Reach 108427 := (sr 1 108427 162641 (by norm_num) (by norm_num) (sr 2 162641 121981 (by norm_num) (by norm_num) (sr 3 121981 45743 (by norm_num) (by norm_num) (B 45743 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108431 : Reach 108431 := (sr 1 108431 162647 (by norm_num) (by norm_num) (sr 1 162647 243971 (by norm_num) (by norm_num) (sr 1 243971 365957 (by norm_num) (by norm_num) (sr 4 365957 68617 (by norm_num) (by norm_num) (B 68617 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108435 : Reach 108435 := (sr 1 108435 162653 (by norm_num) (by norm_num) (sr 3 162653 60995 (by norm_num) (by norm_num) (B 60995 (by norm_num) (by norm_num) (by norm_num))))
theorem R108439 : Reach 108439 := (sr 1 108439 162659 (by norm_num) (by norm_num) (sr 1 162659 243989 (by norm_num) (by norm_num) (sr 6 243989 11437 (by norm_num) (by norm_num) (B 11437 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108443 : Reach 108443 := (sr 1 108443 162665 (by norm_num) (by norm_num) (sr 2 162665 121999 (by norm_num) (by norm_num) (sr 1 121999 182999 (by norm_num) (by norm_num) (sr 1 182999 274499 (by norm_num) (by norm_num) (sr 1 274499 411749 (by norm_num) (by norm_num) (sr 4 411749 77203 (by norm_num) (by norm_num) (B 77203 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108447 : Reach 108447 := (sr 1 108447 162671 (by norm_num) (by norm_num) (sr 1 162671 244007 (by norm_num) (by norm_num) (sr 1 244007 366011 (by norm_num) (by norm_num) (sr 1 366011 549017 (by norm_num) (by norm_num) (sr 2 549017 411763 (by norm_num) (by norm_num) (sr 1 411763 617645 (by norm_num) (by norm_num) (sr 3 617645 231617 (by norm_num) (by norm_num) (sr 2 231617 173713 (by norm_num) (by norm_num) (sr 2 173713 130285 (by norm_num) (by norm_num) (sr 3 130285 48857 (by norm_num) (by norm_num) (B 48857 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R108451 : Reach 108451 := (sr 1 108451 162677 (by norm_num) (by norm_num) (sr 5 162677 15251 (by norm_num) (by norm_num) (B 15251 (by norm_num) (by norm_num) (by norm_num))))
theorem R108455 : Reach 108455 := (sr 1 108455 162683 (by norm_num) (by norm_num) (sr 1 162683 244025 (by norm_num) (by norm_num) (sr 2 244025 183019 (by norm_num) (by norm_num) (sr 1 183019 274529 (by norm_num) (by norm_num) (sr 2 274529 205897 (by norm_num) (by norm_num) (sr 2 205897 154423 (by norm_num) (by norm_num) (sr 1 154423 231635 (by norm_num) (by norm_num) (sr 1 231635 347453 (by norm_num) (by norm_num) (sr 3 347453 130295 (by norm_num) (by norm_num) (sr 1 130295 195443 (by norm_num) (by norm_num) (sr 1 195443 293165 (by norm_num) (by norm_num) (sr 3 293165 109937 (by norm_num) (by norm_num) (sr 2 109937 82453 (by norm_num) (by norm_num) (B 82453 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R108459 : Reach 108459 := (sr 1 108459 162689 (by norm_num) (by norm_num) (sr 2 162689 122017 (by norm_num) (by norm_num) (sr 2 122017 91513 (by norm_num) (by norm_num) (B 91513 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108463 : Reach 108463 := (sr 1 108463 162695 (by norm_num) (by norm_num) (sr 1 162695 244043 (by norm_num) (by norm_num) (sr 1 244043 366065 (by norm_num) (by norm_num) (sr 2 366065 274549 (by norm_num) (by norm_num) (sr 5 274549 25739 (by norm_num) (by norm_num) (B 25739 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R108467 : Reach 108467 := (sr 1 108467 162701 (by norm_num) (by norm_num) (sr 3 162701 61013 (by norm_num) (by norm_num) (B 61013 (by norm_num) (by norm_num) (by norm_num))))
theorem R108471 : Reach 108471 := (sr 1 108471 162707 (by norm_num) (by norm_num) (sr 1 162707 244061 (by norm_num) (by norm_num) (sr 3 244061 91523 (by norm_num) (by norm_num) (B 91523 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108475 : Reach 108475 := (sr 1 108475 162713 (by norm_num) (by norm_num) (sr 2 162713 122035 (by norm_num) (by norm_num) (sr 1 122035 183053 (by norm_num) (by norm_num) (sr 3 183053 68645 (by norm_num) (by norm_num) (B 68645 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108479 : Reach 108479 := (sr 1 108479 162719 (by norm_num) (by norm_num) (sr 1 162719 244079 (by norm_num) (by norm_num) (sr 1 244079 366119 (by norm_num) (by norm_num) (sr 1 366119 549179 (by norm_num) (by norm_num) (sr 1 549179 823769 (by norm_num) (by norm_num) (sr 2 823769 617827 (by norm_num) (by norm_num) (sr 1 617827 926741 (by norm_num) (by norm_num) (sr 6 926741 43441 (by norm_num) (by norm_num) (B 43441 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R108483 : Reach 108483 := (sr 1 108483 162725 (by norm_num) (by norm_num) (sr 4 162725 30511 (by norm_num) (by norm_num) (B 30511 (by norm_num) (by norm_num) (by norm_num))))
theorem R108487 : Reach 108487 := (sr 1 108487 162731 (by norm_num) (by norm_num) (sr 1 162731 244097 (by norm_num) (by norm_num) (sr 2 244097 183073 (by norm_num) (by norm_num) (sr 2 183073 137305 (by norm_num) (by norm_num) (sr 2 137305 102979 (by norm_num) (by norm_num) R102979)))))
theorem R108491 : Reach 108491 := (sr 1 108491 162737 (by norm_num) (by norm_num) (sr 2 162737 122053 (by norm_num) (by norm_num) (sr 4 122053 22885 (by norm_num) (by norm_num) (B 22885 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108495 : Reach 108495 := (sr 1 108495 162743 (by norm_num) (by norm_num) (sr 1 162743 244115 (by norm_num) (by norm_num) (sr 1 244115 366173 (by norm_num) (by norm_num) (sr 3 366173 137315 (by norm_num) (by norm_num) (sr 1 137315 205973 (by norm_num) (by norm_num) (sr 6 205973 9655 (by norm_num) (by norm_num) (B 9655 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108499 : Reach 108499 := (sr 1 108499 162749 (by norm_num) (by norm_num) (sr 3 162749 61031 (by norm_num) (by norm_num) (B 61031 (by norm_num) (by norm_num) (by norm_num))))
theorem R108503 : Reach 108503 := (sr 1 108503 162755 (by norm_num) (by norm_num) (sr 1 162755 244133 (by norm_num) (by norm_num) (sr 4 244133 45775 (by norm_num) (by norm_num) (B 45775 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108507 : Reach 108507 := (sr 1 108507 162761 (by norm_num) (by norm_num) (sr 2 162761 122071 (by norm_num) (by norm_num) (sr 1 122071 183107 (by norm_num) (by norm_num) (sr 1 183107 274661 (by norm_num) (by norm_num) (sr 4 274661 51499 (by norm_num) (by norm_num) (B 51499 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R108511 : Reach 108511 := (sr 1 108511 162767 (by norm_num) (by norm_num) (sr 1 162767 244151 (by norm_num) (by norm_num) (sr 1 244151 366227 (by norm_num) (by norm_num) (sr 1 366227 549341 (by norm_num) (by norm_num) (sr 3 549341 206003 (by norm_num) (by norm_num) (sr 1 206003 309005 (by norm_num) (by norm_num) (sr 3 309005 115877 (by norm_num) (by norm_num) (sr 4 115877 21727 (by norm_num) (by norm_num) (B 21727 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R108515 : Reach 108515 := (sr 1 108515 162773 (by norm_num) (by norm_num) (sr 7 162773 3815 (by norm_num) (by norm_num) (B 3815 (by norm_num) (by norm_num) (by norm_num))))
theorem R108519 : Reach 108519 := (sr 1 108519 162779 (by norm_num) (by norm_num) (sr 1 162779 244169 (by norm_num) (by norm_num) (sr 2 244169 183127 (by norm_num) (by norm_num) (sr 1 183127 274691 (by norm_num) (by norm_num) (sr 1 274691 412037 (by norm_num) (by norm_num) (sr 4 412037 77257 (by norm_num) (by norm_num) (B 77257 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108523 : Reach 108523 := (sr 1 108523 162785 (by norm_num) (by norm_num) (sr 2 162785 122089 (by norm_num) (by norm_num) (sr 2 122089 91567 (by norm_num) (by norm_num) (B 91567 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108527 : Reach 108527 := (sr 1 108527 162791 (by norm_num) (by norm_num) (sr 1 162791 244187 (by norm_num) (by norm_num) (sr 1 244187 366281 (by norm_num) (by norm_num) (sr 2 366281 274711 (by norm_num) (by norm_num) (sr 1 274711 412067 (by norm_num) (by norm_num) (sr 1 412067 618101 (by norm_num) (by norm_num) (sr 5 618101 57947 (by norm_num) (by norm_num) (B 57947 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R108531 : Reach 108531 := (sr 1 108531 162797 (by norm_num) (by norm_num) (sr 3 162797 61049 (by norm_num) (by norm_num) (B 61049 (by norm_num) (by norm_num) (by norm_num))))
theorem R108535 : Reach 108535 := (sr 1 108535 162803 (by norm_num) (by norm_num) (sr 1 162803 244205 (by norm_num) (by norm_num) (sr 3 244205 91577 (by norm_num) (by norm_num) (B 91577 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108539 : Reach 108539 := (sr 1 108539 162809 (by norm_num) (by norm_num) (sr 2 162809 122107 (by norm_num) (by norm_num) (sr 1 122107 183161 (by norm_num) (by norm_num) (sr 2 183161 137371 (by norm_num) (by norm_num) (sr 1 137371 206057 (by norm_num) (by norm_num) (sr 2 206057 154543 (by norm_num) (by norm_num) (sr 1 154543 231815 (by norm_num) (by norm_num) (sr 1 231815 347723 (by norm_num) (by norm_num) (sr 1 347723 521585 (by norm_num) (by norm_num) (sr 2 521585 391189 (by norm_num) (by norm_num) (sr 6 391189 18337 (by norm_num) (by norm_num) (B 18337 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R108543 : Reach 108543 := (sr 1 108543 162815 (by norm_num) (by norm_num) (sr 1 162815 244223 (by norm_num) (by norm_num) (sr 1 244223 366335 (by norm_num) (by norm_num) (sr 1 366335 549503 (by norm_num) (by norm_num) (sr 1 549503 824255 (by norm_num) (by norm_num) (sr 1 824255 1236383 (by norm_num) (by norm_num) (sr 1 1236383 1854575 (by norm_num) (by norm_num) (sr 1 1854575 2781863 (by norm_num) (by norm_num) (sr 1 2781863 4172795 (by norm_num) (by norm_num) (sr 1 4172795 6259193 (by norm_num) (by norm_num) (sr 2 6259193 4694395 (by norm_num) (by norm_num) (sr 1 4694395 7041593 (by norm_num) (by norm_num) (sr 2 7041593 5281195 (by norm_num) (by norm_num) (sr 1 5281195 7921793 (by norm_num) (by norm_num) (sr 2 7921793 5941345 (by norm_num) (by norm_num) (sr 2 5941345 4456009 (by norm_num) (by norm_num) (sr 2 4456009 3342007 (by norm_num) (by norm_num) (sr 1 3342007 5013011 (by norm_num) (by norm_num) (sr 1 5013011 7519517 (by norm_num) (by norm_num) (sr 3 7519517 2819819 (by norm_num) (by norm_num) (sr 1 2819819 4229729 (by norm_num) (by norm_num) (sr 2 4229729 3172297 (by norm_num) (by norm_num) (sr 2 3172297 2379223 (by norm_num) (by norm_num) (sr 1 2379223 3568835 (by norm_num) (by norm_num) (sr 1 3568835 5353253 (by norm_num) (by norm_num) (sr 4 5353253 1003735 (by norm_num) (by norm_num) (sr 1 1003735 1505603 (by norm_num) (by norm_num) (sr 1 1505603 2258405 (by norm_num) (by norm_num) (sr 4 2258405 423451 (by norm_num) (by norm_num) (sr 1 423451 635177 (by norm_num) (by norm_num) (sr 2 635177 476383 (by norm_num) (by norm_num) (sr 1 476383 714575 (by norm_num) (by norm_num) (sr 1 714575 1071863 (by norm_num) (by norm_num) (sr 1 1071863 1607795 (by norm_num) (by norm_num) (sr 1 1607795 2411693 (by norm_num) (by norm_num) (sr 3 2411693 904385 (by norm_num) (by norm_num) (sr 2 904385 678289 (by norm_num) (by norm_num) (sr 2 678289 508717 (by norm_num) (by norm_num) (sr 3 508717 190769 (by norm_num) (by norm_num) (sr 2 190769 143077 (by norm_num) (by norm_num) (sr 4 143077 26827 (by norm_num) (by norm_num) (B 26827 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))))))))))))))
theorem R108547 : Reach 108547 := (sr 1 108547 162821 (by norm_num) (by norm_num) (sr 4 162821 30529 (by norm_num) (by norm_num) (B 30529 (by norm_num) (by norm_num) (by norm_num))))
theorem R108551 : Reach 108551 := (sr 1 108551 162827 (by norm_num) (by norm_num) (sr 1 162827 244241 (by norm_num) (by norm_num) (sr 2 244241 183181 (by norm_num) (by norm_num) (sr 3 183181 68693 (by norm_num) (by norm_num) (B 68693 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108555 : Reach 108555 := (sr 1 108555 162833 (by norm_num) (by norm_num) (sr 2 162833 122125 (by norm_num) (by norm_num) (sr 3 122125 45797 (by norm_num) (by norm_num) (B 45797 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108559 : Reach 108559 := (sr 1 108559 162839 (by norm_num) (by norm_num) (sr 1 162839 244259 (by norm_num) (by norm_num) (sr 1 244259 366389 (by norm_num) (by norm_num) (sr 5 366389 34349 (by norm_num) (by norm_num) (B 34349 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108563 : Reach 108563 := (sr 1 108563 162845 (by norm_num) (by norm_num) (sr 3 162845 61067 (by norm_num) (by norm_num) (B 61067 (by norm_num) (by norm_num) (by norm_num))))
theorem R108567 : Reach 108567 := (sr 1 108567 162851 (by norm_num) (by norm_num) (sr 1 162851 244277 (by norm_num) (by norm_num) (sr 5 244277 22901 (by norm_num) (by norm_num) (B 22901 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108571 : Reach 108571 := (sr 1 108571 162857 (by norm_num) (by norm_num) (sr 2 162857 122143 (by norm_num) (by norm_num) (sr 1 122143 183215 (by norm_num) (by norm_num) (sr 1 183215 274823 (by norm_num) (by norm_num) (sr 1 274823 412235 (by norm_num) (by norm_num) (sr 1 412235 618353 (by norm_num) (by norm_num) (sr 2 618353 463765 (by norm_num) (by norm_num) (sr 6 463765 21739 (by norm_num) (by norm_num) (B 21739 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R108575 : Reach 108575 := (sr 1 108575 162863 (by norm_num) (by norm_num) (sr 1 162863 244295 (by norm_num) (by norm_num) (sr 1 244295 366443 (by norm_num) (by norm_num) (sr 1 366443 549665 (by norm_num) (by norm_num) (sr 2 549665 412249 (by norm_num) (by norm_num) (sr 2 412249 309187 (by norm_num) (by norm_num) (sr 1 309187 463781 (by norm_num) (by norm_num) (sr 4 463781 86959 (by norm_num) (by norm_num) (B 86959 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R108579 : Reach 108579 := (sr 1 108579 162869 (by norm_num) (by norm_num) (sr 5 162869 15269 (by norm_num) (by norm_num) (B 15269 (by norm_num) (by norm_num) (by norm_num))))
theorem R108583 : Reach 108583 := (sr 1 108583 162875 (by norm_num) (by norm_num) (sr 1 162875 244313 (by norm_num) (by norm_num) (sr 2 244313 183235 (by norm_num) (by norm_num) (sr 1 183235 274853 (by norm_num) (by norm_num) (sr 4 274853 51535 (by norm_num) (by norm_num) (B 51535 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R108587 : Reach 108587 := (sr 1 108587 162881 (by norm_num) (by norm_num) (sr 2 162881 122161 (by norm_num) (by norm_num) (sr 2 122161 91621 (by norm_num) (by norm_num) (B 91621 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108591 : Reach 108591 := (sr 1 108591 162887 (by norm_num) (by norm_num) (sr 1 162887 244331 (by norm_num) (by norm_num) (sr 1 244331 366497 (by norm_num) (by norm_num) (sr 2 366497 274873 (by norm_num) (by norm_num) (sr 2 274873 206155 (by norm_num) (by norm_num) (sr 1 206155 309233 (by norm_num) (by norm_num) (sr 2 309233 231925 (by norm_num) (by norm_num) (sr 5 231925 21743 (by norm_num) (by norm_num) (B 21743 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R108595 : Reach 108595 := (sr 1 108595 162893 (by norm_num) (by norm_num) (sr 3 162893 61085 (by norm_num) (by norm_num) (B 61085 (by norm_num) (by norm_num) (by norm_num))))
theorem R108599 : Reach 108599 := (sr 1 108599 162899 (by norm_num) (by norm_num) (sr 1 162899 244349 (by norm_num) (by norm_num) (sr 3 244349 91631 (by norm_num) (by norm_num) (B 91631 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108603 : Reach 108603 := (sr 1 108603 162905 (by norm_num) (by norm_num) (sr 2 162905 122179 (by norm_num) (by norm_num) (sr 1 122179 183269 (by norm_num) (by norm_num) (sr 4 183269 34363 (by norm_num) (by norm_num) (B 34363 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108607 : Reach 108607 := (sr 1 108607 162911 (by norm_num) (by norm_num) (sr 1 162911 244367 (by norm_num) (by norm_num) (sr 1 244367 366551 (by norm_num) (by norm_num) (sr 1 366551 549827 (by norm_num) (by norm_num) (sr 1 549827 824741 (by norm_num) (by norm_num) (sr 4 824741 154639 (by norm_num) (by norm_num) (sr 1 154639 231959 (by norm_num) (by norm_num) (sr 1 231959 347939 (by norm_num) (by norm_num) (sr 1 347939 521909 (by norm_num) (by norm_num) (sr 5 521909 48929 (by norm_num) (by norm_num) (B 48929 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R108611 : Reach 108611 := (sr 1 108611 162917 (by norm_num) (by norm_num) (sr 4 162917 30547 (by norm_num) (by norm_num) (B 30547 (by norm_num) (by norm_num) (by norm_num))))
theorem R108615 : Reach 108615 := (sr 1 108615 162923 (by norm_num) (by norm_num) (sr 1 162923 244385 (by norm_num) (by norm_num) (sr 2 244385 183289 (by norm_num) (by norm_num) (sr 2 183289 137467 (by norm_num) (by norm_num) (sr 1 137467 206201 (by norm_num) (by norm_num) (sr 2 206201 154651 (by norm_num) (by norm_num) (sr 1 154651 231977 (by norm_num) (by norm_num) (sr 2 231977 173983 (by norm_num) (by norm_num) (sr 1 173983 260975 (by norm_num) (by norm_num) (sr 1 260975 391463 (by norm_num) (by norm_num) (sr 1 391463 587195 (by norm_num) (by norm_num) (sr 1 587195 880793 (by norm_num) (by norm_num) (sr 2 880793 660595 (by norm_num) (by norm_num) (sr 1 660595 990893 (by norm_num) (by norm_num) (sr 3 990893 371585 (by norm_num) (by norm_num) (sr 2 371585 278689 (by norm_num) (by norm_num) (sr 2 278689 209017 (by norm_num) (by norm_num) (sr 2 209017 156763 (by norm_num) (by norm_num) (sr 1 156763 235145 (by norm_num) (by norm_num) (sr 2 235145 176359 (by norm_num) (by norm_num) (sr 1 176359 264539 (by norm_num) (by norm_num) (sr 1 264539 396809 (by norm_num) (by norm_num) (sr 2 396809 297607 (by norm_num) (by norm_num) (sr 1 297607 446411 (by norm_num) (by norm_num) (sr 1 446411 669617 (by norm_num) (by norm_num) (sr 2 669617 502213 (by norm_num) (by norm_num) (sr 4 502213 94165 (by norm_num) (by norm_num) (B 94165 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))
theorem R108619 : Reach 108619 := (sr 1 108619 162929 (by norm_num) (by norm_num) (sr 2 162929 122197 (by norm_num) (by norm_num) (sr 11 122197 179 (by norm_num) (by norm_num) (B 179 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108623 : Reach 108623 := (sr 1 108623 162935 (by norm_num) (by norm_num) (sr 1 162935 244403 (by norm_num) (by norm_num) (sr 1 244403 366605 (by norm_num) (by norm_num) (sr 3 366605 137477 (by norm_num) (by norm_num) (sr 4 137477 25777 (by norm_num) (by norm_num) (B 25777 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R108627 : Reach 108627 := (sr 1 108627 162941 (by norm_num) (by norm_num) (sr 3 162941 61103 (by norm_num) (by norm_num) (B 61103 (by norm_num) (by norm_num) (by norm_num))))
theorem R108631 : Reach 108631 := (sr 1 108631 162947 (by norm_num) (by norm_num) (sr 1 162947 244421 (by norm_num) (by norm_num) (sr 4 244421 45829 (by norm_num) (by norm_num) (B 45829 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108635 : Reach 108635 := (sr 1 108635 162953 (by norm_num) (by norm_num) (sr 2 162953 122215 (by norm_num) (by norm_num) (sr 1 122215 183323 (by norm_num) (by norm_num) (sr 1 183323 274985 (by norm_num) (by norm_num) (sr 2 274985 206239 (by norm_num) (by norm_num) (sr 1 206239 309359 (by norm_num) (by norm_num) (sr 1 309359 464039 (by norm_num) (by norm_num) (sr 1 464039 696059 (by norm_num) (by norm_num) (sr 1 696059 1044089 (by norm_num) (by norm_num) (sr 2 1044089 783067 (by norm_num) (by norm_num) (sr 1 783067 1174601 (by norm_num) (by norm_num) (sr 2 1174601 880951 (by norm_num) (by norm_num) (sr 1 880951 1321427 (by norm_num) (by norm_num) (sr 1 1321427 1982141 (by norm_num) (by norm_num) (sr 3 1982141 743303 (by norm_num) (by norm_num) (sr 1 743303 1114955 (by norm_num) (by norm_num) (sr 1 1114955 1672433 (by norm_num) (by norm_num) (sr 2 1672433 1254325 (by norm_num) (by norm_num) (sr 5 1254325 117593 (by norm_num) (by norm_num) (sr 2 117593 88195 (by norm_num) (by norm_num) (B 88195 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))
theorem R108639 : Reach 108639 := (sr 1 108639 162959 (by norm_num) (by norm_num) (sr 1 162959 244439 (by norm_num) (by norm_num) (sr 1 244439 366659 (by norm_num) (by norm_num) (sr 1 366659 549989 (by norm_num) (by norm_num) (sr 4 549989 103123 (by norm_num) (by norm_num) R103123)))))
theorem R108643 : Reach 108643 := (sr 1 108643 162965 (by norm_num) (by norm_num) (sr 6 162965 7639 (by norm_num) (by norm_num) (B 7639 (by norm_num) (by norm_num) (by norm_num))))
theorem R108647 : Reach 108647 := (sr 1 108647 162971 (by norm_num) (by norm_num) (sr 1 162971 244457 (by norm_num) (by norm_num) (sr 2 244457 183343 (by norm_num) (by norm_num) (sr 1 183343 275015 (by norm_num) (by norm_num) (sr 1 275015 412523 (by norm_num) (by norm_num) (sr 1 412523 618785 (by norm_num) (by norm_num) (sr 2 618785 464089 (by norm_num) (by norm_num) (sr 2 464089 348067 (by norm_num) (by norm_num) (sr 1 348067 522101 (by norm_num) (by norm_num) (sr 5 522101 48947 (by norm_num) (by norm_num) (B 48947 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R108651 : Reach 108651 := (sr 1 108651 162977 (by norm_num) (by norm_num) (sr 2 162977 122233 (by norm_num) (by norm_num) (sr 2 122233 91675 (by norm_num) (by norm_num) (B 91675 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108655 : Reach 108655 := (sr 1 108655 162983 (by norm_num) (by norm_num) (sr 1 162983 244475 (by norm_num) (by norm_num) (sr 1 244475 366713 (by norm_num) (by norm_num) (sr 2 366713 275035 (by norm_num) (by norm_num) (sr 1 275035 412553 (by norm_num) (by norm_num) (sr 2 412553 309415 (by norm_num) (by norm_num) (sr 1 309415 464123 (by norm_num) (by norm_num) (sr 1 464123 696185 (by norm_num) (by norm_num) (sr 2 696185 522139 (by norm_num) (by norm_num) (sr 1 522139 783209 (by norm_num) (by norm_num) (sr 2 783209 587407 (by norm_num) (by norm_num) (sr 1 587407 881111 (by norm_num) (by norm_num) (sr 1 881111 1321667 (by norm_num) (by norm_num) (sr 1 1321667 1982501 (by norm_num) (by norm_num) (sr 4 1982501 371719 (by norm_num) (by norm_num) (sr 1 371719 557579 (by norm_num) (by norm_num) (sr 1 557579 836369 (by norm_num) (by norm_num) (sr 2 836369 627277 (by norm_num) (by norm_num) (sr 3 627277 235229 (by norm_num) (by norm_num) (sr 3 235229 88211 (by norm_num) (by norm_num) (B 88211 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))
theorem R108659 : Reach 108659 := (sr 1 108659 162989 (by norm_num) (by norm_num) (sr 3 162989 61121 (by norm_num) (by norm_num) (B 61121 (by norm_num) (by norm_num) (by norm_num))))
theorem R108663 : Reach 108663 := (sr 1 108663 162995 (by norm_num) (by norm_num) (sr 1 162995 244493 (by norm_num) (by norm_num) (sr 3 244493 91685 (by norm_num) (by norm_num) (B 91685 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108667 : Reach 108667 := (sr 1 108667 163001 (by norm_num) (by norm_num) (sr 2 163001 122251 (by norm_num) (by norm_num) (sr 1 122251 183377 (by norm_num) (by norm_num) (sr 2 183377 137533 (by norm_num) (by norm_num) (sr 3 137533 51575 (by norm_num) (by norm_num) (B 51575 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R108671 : Reach 108671 := (sr 1 108671 163007 (by norm_num) (by norm_num) (sr 1 163007 244511 (by norm_num) (by norm_num) (sr 1 244511 366767 (by norm_num) (by norm_num) (sr 1 366767 550151 (by norm_num) (by norm_num) (sr 1 550151 825227 (by norm_num) (by norm_num) (sr 1 825227 1237841 (by norm_num) (by norm_num) (sr 2 1237841 928381 (by norm_num) (by norm_num) (sr 3 928381 348143 (by norm_num) (by norm_num) (sr 1 348143 522215 (by norm_num) (by norm_num) (sr 1 522215 783323 (by norm_num) (by norm_num) (sr 1 783323 1174985 (by norm_num) (by norm_num) (sr 2 1174985 881239 (by norm_num) (by norm_num) (sr 1 881239 1321859 (by norm_num) (by norm_num) (sr 1 1321859 1982789 (by norm_num) (by norm_num) (sr 4 1982789 371773 (by norm_num) (by norm_num) (sr 3 371773 139415 (by norm_num) (by norm_num) (sr 1 139415 209123 (by norm_num) (by norm_num) (sr 1 209123 313685 (by norm_num) (by norm_num) (sr 10 313685 919 (by norm_num) (by norm_num) (B 919 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))
theorem R108675 : Reach 108675 := (sr 1 108675 163013 (by norm_num) (by norm_num) (sr 4 163013 30565 (by norm_num) (by norm_num) (B 30565 (by norm_num) (by norm_num) (by norm_num))))
theorem R108679 : Reach 108679 := (sr 1 108679 163019 (by norm_num) (by norm_num) (sr 1 163019 244529 (by norm_num) (by norm_num) (sr 2 244529 183397 (by norm_num) (by norm_num) (sr 4 183397 34387 (by norm_num) (by norm_num) (B 34387 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108683 : Reach 108683 := (sr 1 108683 163025 (by norm_num) (by norm_num) (sr 2 163025 122269 (by norm_num) (by norm_num) (sr 3 122269 45851 (by norm_num) (by norm_num) (B 45851 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108687 : Reach 108687 := (sr 1 108687 163031 (by norm_num) (by norm_num) (sr 1 163031 244547 (by norm_num) (by norm_num) (sr 1 244547 366821 (by norm_num) (by norm_num) (sr 4 366821 68779 (by norm_num) (by norm_num) (B 68779 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108691 : Reach 108691 := (sr 1 108691 163037 (by norm_num) (by norm_num) (sr 3 163037 61139 (by norm_num) (by norm_num) (B 61139 (by norm_num) (by norm_num) (by norm_num))))
theorem R108695 : Reach 108695 := (sr 1 108695 163043 (by norm_num) (by norm_num) (sr 1 163043 244565 (by norm_num) (by norm_num) (sr 9 244565 1433 (by norm_num) (by norm_num) (B 1433 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108699 : Reach 108699 := (sr 1 108699 163049 (by norm_num) (by norm_num) (sr 2 163049 122287 (by norm_num) (by norm_num) (sr 1 122287 183431 (by norm_num) (by norm_num) (sr 1 183431 275147 (by norm_num) (by norm_num) (sr 1 275147 412721 (by norm_num) (by norm_num) (sr 2 412721 309541 (by norm_num) (by norm_num) (sr 4 309541 58039 (by norm_num) (by norm_num) (B 58039 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R108703 : Reach 108703 := (sr 1 108703 163055 (by norm_num) (by norm_num) (sr 1 163055 244583 (by norm_num) (by norm_num) (sr 1 244583 366875 (by norm_num) (by norm_num) (sr 1 366875 550313 (by norm_num) (by norm_num) (sr 2 550313 412735 (by norm_num) (by norm_num) (sr 1 412735 619103 (by norm_num) (by norm_num) (sr 1 619103 928655 (by norm_num) (by norm_num) (sr 1 928655 1392983 (by norm_num) (by norm_num) (sr 1 1392983 2089475 (by norm_num) (by norm_num) (sr 1 2089475 3134213 (by norm_num) (by norm_num) (sr 4 3134213 587665 (by norm_num) (by norm_num) (sr 2 587665 440749 (by norm_num) (by norm_num) (sr 3 440749 165281 (by norm_num) (by norm_num) (sr 2 165281 123961 (by norm_num) (by norm_num) (sr 2 123961 92971 (by norm_num) (by norm_num) (B 92971 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R108707 : Reach 108707 := (sr 1 108707 163061 (by norm_num) (by norm_num) (sr 5 163061 15287 (by norm_num) (by norm_num) (B 15287 (by norm_num) (by norm_num) (by norm_num))))
theorem R108711 : Reach 108711 := (sr 1 108711 163067 (by norm_num) (by norm_num) (sr 1 163067 244601 (by norm_num) (by norm_num) (sr 2 244601 183451 (by norm_num) (by norm_num) (sr 1 183451 275177 (by norm_num) (by norm_num) (sr 2 275177 206383 (by norm_num) (by norm_num) (sr 1 206383 309575 (by norm_num) (by norm_num) (sr 1 309575 464363 (by norm_num) (by norm_num) (sr 1 464363 696545 (by norm_num) (by norm_num) (sr 2 696545 522409 (by norm_num) (by norm_num) (sr 2 522409 391807 (by norm_num) (by norm_num) (sr 1 391807 587711 (by norm_num) (by norm_num) (sr 1 587711 881567 (by norm_num) (by norm_num) (sr 1 881567 1322351 (by norm_num) (by norm_num) (sr 1 1322351 1983527 (by norm_num) (by norm_num) (sr 1 1983527 2975291 (by norm_num) (by norm_num) (sr 1 2975291 4462937 (by norm_num) (by norm_num) (sr 2 4462937 3347203 (by norm_num) (by norm_num) (sr 1 3347203 5020805 (by norm_num) (by norm_num) (sr 4 5020805 941401 (by norm_num) (by norm_num) (sr 2 941401 706051 (by norm_num) (by norm_num) (sr 1 706051 1059077 (by norm_num) (by norm_num) (sr 4 1059077 198577 (by norm_num) (by norm_num) (sr 2 198577 148933 (by norm_num) (by norm_num) (sr 4 148933 27925 (by norm_num) (by norm_num) (B 27925 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))
theorem R108715 : Reach 108715 := (sr 1 108715 163073 (by norm_num) (by norm_num) (sr 2 163073 122305 (by norm_num) (by norm_num) (sr 2 122305 91729 (by norm_num) (by norm_num) (B 91729 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108719 : Reach 108719 := (sr 1 108719 163079 (by norm_num) (by norm_num) (sr 1 163079 244619 (by norm_num) (by norm_num) (sr 1 244619 366929 (by norm_num) (by norm_num) (sr 2 366929 275197 (by norm_num) (by norm_num) (sr 3 275197 103199 (by norm_num) (by norm_num) R103199)))))
theorem R108723 : Reach 108723 := (sr 1 108723 163085 (by norm_num) (by norm_num) (sr 3 163085 61157 (by norm_num) (by norm_num) (B 61157 (by norm_num) (by norm_num) (by norm_num))))
theorem R108727 : Reach 108727 := (sr 1 108727 163091 (by norm_num) (by norm_num) (sr 1 163091 244637 (by norm_num) (by norm_num) (sr 3 244637 91739 (by norm_num) (by norm_num) (B 91739 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108731 : Reach 108731 := (sr 1 108731 163097 (by norm_num) (by norm_num) (sr 2 163097 122323 (by norm_num) (by norm_num) (sr 1 122323 183485 (by norm_num) (by norm_num) (sr 3 183485 68807 (by norm_num) (by norm_num) (B 68807 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108735 : Reach 108735 := (sr 1 108735 163103 (by norm_num) (by norm_num) (sr 1 163103 244655 (by norm_num) (by norm_num) (sr 1 244655 366983 (by norm_num) (by norm_num) (sr 1 366983 550475 (by norm_num) (by norm_num) (sr 1 550475 825713 (by norm_num) (by norm_num) (sr 2 825713 619285 (by norm_num) (by norm_num) (sr 6 619285 29029 (by norm_num) (by norm_num) (B 29029 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R108739 : Reach 108739 := (sr 1 108739 163109 (by norm_num) (by norm_num) (sr 4 163109 30583 (by norm_num) (by norm_num) (B 30583 (by norm_num) (by norm_num) (by norm_num))))
theorem R108743 : Reach 108743 := (sr 1 108743 163115 (by norm_num) (by norm_num) (sr 1 163115 244673 (by norm_num) (by norm_num) (sr 2 244673 183505 (by norm_num) (by norm_num) (sr 2 183505 137629 (by norm_num) (by norm_num) (sr 3 137629 51611 (by norm_num) (by norm_num) (B 51611 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R108747 : Reach 108747 := (sr 1 108747 163121 (by norm_num) (by norm_num) (sr 2 163121 122341 (by norm_num) (by norm_num) (sr 4 122341 22939 (by norm_num) (by norm_num) (B 22939 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108751 : Reach 108751 := (sr 1 108751 163127 (by norm_num) (by norm_num) (sr 1 163127 244691 (by norm_num) (by norm_num) (sr 1 244691 367037 (by norm_num) (by norm_num) (sr 3 367037 137639 (by norm_num) (by norm_num) (sr 1 137639 206459 (by norm_num) (by norm_num) (sr 1 206459 309689 (by norm_num) (by norm_num) (sr 2 309689 232267 (by norm_num) (by norm_num) (sr 1 232267 348401 (by norm_num) (by norm_num) (sr 2 348401 261301 (by norm_num) (by norm_num) (sr 5 261301 24497 (by norm_num) (by norm_num) (B 24497 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R108755 : Reach 108755 := (sr 1 108755 163133 (by norm_num) (by norm_num) (sr 3 163133 61175 (by norm_num) (by norm_num) (B 61175 (by norm_num) (by norm_num) (by norm_num))))
theorem R108759 : Reach 108759 := (sr 1 108759 163139 (by norm_num) (by norm_num) (sr 1 163139 244709 (by norm_num) (by norm_num) (sr 4 244709 45883 (by norm_num) (by norm_num) (B 45883 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108763 : Reach 108763 := (sr 1 108763 163145 (by norm_num) (by norm_num) (sr 2 163145 122359 (by norm_num) (by norm_num) (sr 1 122359 183539 (by norm_num) (by norm_num) (sr 1 183539 275309 (by norm_num) (by norm_num) (sr 3 275309 103241 (by norm_num) (by norm_num) (sr 2 103241 77431 (by norm_num) (by norm_num) (B 77431 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108767 : Reach 108767 := (sr 1 108767 163151 (by norm_num) (by norm_num) (sr 1 163151 244727 (by norm_num) (by norm_num) (sr 1 244727 367091 (by norm_num) (by norm_num) (sr 1 367091 550637 (by norm_num) (by norm_num) (sr 3 550637 206489 (by norm_num) (by norm_num) (sr 2 206489 154867 (by norm_num) (by norm_num) (sr 1 154867 232301 (by norm_num) (by norm_num) (sr 3 232301 87113 (by norm_num) (by norm_num) (B 87113 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R108771 : Reach 108771 := (sr 1 108771 163157 (by norm_num) (by norm_num) (sr 11 163157 239 (by norm_num) (by norm_num) (B 239 (by norm_num) (by norm_num) (by norm_num))))
theorem R108775 : Reach 108775 := (sr 1 108775 163163 (by norm_num) (by norm_num) (sr 1 163163 244745 (by norm_num) (by norm_num) (sr 2 244745 183559 (by norm_num) (by norm_num) (sr 1 183559 275339 (by norm_num) (by norm_num) (sr 1 275339 413009 (by norm_num) (by norm_num) (sr 2 413009 309757 (by norm_num) (by norm_num) (sr 3 309757 116159 (by norm_num) (by norm_num) (sr 1 116159 174239 (by norm_num) (by norm_num) (sr 1 174239 261359 (by norm_num) (by norm_num) (sr 1 261359 392039 (by norm_num) (by norm_num) (sr 1 392039 588059 (by norm_num) (by norm_num) (sr 1 588059 882089 (by norm_num) (by norm_num) (sr 2 882089 661567 (by norm_num) (by norm_num) (sr 1 661567 992351 (by norm_num) (by norm_num) (sr 1 992351 1488527 (by norm_num) (by norm_num) (sr 1 1488527 2232791 (by norm_num) (by norm_num) (sr 1 2232791 3349187 (by norm_num) (by norm_num) (sr 1 3349187 5023781 (by norm_num) (by norm_num) (sr 4 5023781 941959 (by norm_num) (by norm_num) (sr 1 941959 1412939 (by norm_num) (by norm_num) (sr 1 1412939 2119409 (by norm_num) (by norm_num) (sr 2 2119409 1589557 (by norm_num) (by norm_num) (sr 5 1589557 149021 (by norm_num) (by norm_num) (sr 3 149021 55883 (by norm_num) (by norm_num) (B 55883 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))
theorem R108779 : Reach 108779 := (sr 1 108779 163169 (by norm_num) (by norm_num) (sr 2 163169 122377 (by norm_num) (by norm_num) (sr 2 122377 91783 (by norm_num) (by norm_num) (B 91783 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108783 : Reach 108783 := (sr 1 108783 163175 (by norm_num) (by norm_num) (sr 1 163175 244763 (by norm_num) (by norm_num) (sr 1 244763 367145 (by norm_num) (by norm_num) (sr 2 367145 275359 (by norm_num) (by norm_num) (sr 1 275359 413039 (by norm_num) (by norm_num) (sr 1 413039 619559 (by norm_num) (by norm_num) (sr 1 619559 929339 (by norm_num) (by norm_num) (sr 1 929339 1394009 (by norm_num) (by norm_num) (sr 2 1394009 1045507 (by norm_num) (by norm_num) (sr 1 1045507 1568261 (by norm_num) (by norm_num) (sr 4 1568261 294049 (by norm_num) (by norm_num) (sr 2 294049 220537 (by norm_num) (by norm_num) (sr 2 220537 165403 (by norm_num) (by norm_num) (sr 1 165403 248105 (by norm_num) (by norm_num) (sr 2 248105 186079 (by norm_num) (by norm_num) (sr 1 186079 279119 (by norm_num) (by norm_num) (sr 1 279119 418679 (by norm_num) (by norm_num) (sr 1 418679 628019 (by norm_num) (by norm_num) (sr 1 628019 942029 (by norm_num) (by norm_num) (sr 3 942029 353261 (by norm_num) (by norm_num) (sr 3 353261 132473 (by norm_num) (by norm_num) (sr 2 132473 99355 (by norm_num) (by norm_num) (B 99355 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))
theorem R108787 : Reach 108787 := (sr 1 108787 163181 (by norm_num) (by norm_num) (sr 3 163181 61193 (by norm_num) (by norm_num) (B 61193 (by norm_num) (by norm_num) (by norm_num))))
theorem R108791 : Reach 108791 := (sr 1 108791 163187 (by norm_num) (by norm_num) (sr 1 163187 244781 (by norm_num) (by norm_num) (sr 3 244781 91793 (by norm_num) (by norm_num) (B 91793 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108795 : Reach 108795 := (sr 1 108795 163193 (by norm_num) (by norm_num) (sr 2 163193 122395 (by norm_num) (by norm_num) (sr 1 122395 183593 (by norm_num) (by norm_num) (sr 2 183593 137695 (by norm_num) (by norm_num) (sr 1 137695 206543 (by norm_num) (by norm_num) (sr 1 206543 309815 (by norm_num) (by norm_num) (sr 1 309815 464723 (by norm_num) (by norm_num) (sr 1 464723 697085 (by norm_num) (by norm_num) (sr 3 697085 261407 (by norm_num) (by norm_num) (sr 1 261407 392111 (by norm_num) (by norm_num) (sr 1 392111 588167 (by norm_num) (by norm_num) (sr 1 588167 882251 (by norm_num) (by norm_num) (sr 1 882251 1323377 (by norm_num) (by norm_num) (sr 2 1323377 992533 (by norm_num) (by norm_num) (sr 6 992533 46525 (by norm_num) (by norm_num) (B 46525 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R108799 : Reach 108799 := (sr 1 108799 163199 (by norm_num) (by norm_num) (sr 1 163199 244799 (by norm_num) (by norm_num) (sr 1 244799 367199 (by norm_num) (by norm_num) (sr 1 367199 550799 (by norm_num) (by norm_num) (sr 1 550799 826199 (by norm_num) (by norm_num) (sr 1 826199 1239299 (by norm_num) (by norm_num) (sr 1 1239299 1858949 (by norm_num) (by norm_num) (sr 4 1858949 348553 (by norm_num) (by norm_num) (sr 2 348553 261415 (by norm_num) (by norm_num) (sr 1 261415 392123 (by norm_num) (by norm_num) (sr 1 392123 588185 (by norm_num) (by norm_num) (sr 2 588185 441139 (by norm_num) (by norm_num) (sr 1 441139 661709 (by norm_num) (by norm_num) (sr 3 661709 248141 (by norm_num) (by norm_num) (sr 3 248141 93053 (by norm_num) (by norm_num) (B 93053 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R108803 : Reach 108803 := (sr 1 108803 163205 (by norm_num) (by norm_num) (sr 4 163205 30601 (by norm_num) (by norm_num) (B 30601 (by norm_num) (by norm_num) (by norm_num))))
theorem R108807 : Reach 108807 := (sr 1 108807 163211 (by norm_num) (by norm_num) (sr 1 163211 244817 (by norm_num) (by norm_num) (sr 2 244817 183613 (by norm_num) (by norm_num) (sr 3 183613 68855 (by norm_num) (by norm_num) (B 68855 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108811 : Reach 108811 := (sr 1 108811 163217 (by norm_num) (by norm_num) (sr 2 163217 122413 (by norm_num) (by norm_num) (sr 3 122413 45905 (by norm_num) (by norm_num) (B 45905 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108815 : Reach 108815 := (sr 1 108815 163223 (by norm_num) (by norm_num) (sr 1 163223 244835 (by norm_num) (by norm_num) (sr 1 244835 367253 (by norm_num) (by norm_num) (sr 6 367253 17215 (by norm_num) (by norm_num) (B 17215 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108819 : Reach 108819 := (sr 1 108819 163229 (by norm_num) (by norm_num) (sr 3 163229 61211 (by norm_num) (by norm_num) (B 61211 (by norm_num) (by norm_num) (by norm_num))))
theorem R108823 : Reach 108823 := (sr 1 108823 163235 (by norm_num) (by norm_num) (sr 1 163235 244853 (by norm_num) (by norm_num) (sr 5 244853 22955 (by norm_num) (by norm_num) (B 22955 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108827 : Reach 108827 := (sr 1 108827 163241 (by norm_num) (by norm_num) (sr 2 163241 122431 (by norm_num) (by norm_num) (sr 1 122431 183647 (by norm_num) (by norm_num) (sr 1 183647 275471 (by norm_num) (by norm_num) (sr 1 275471 413207 (by norm_num) (by norm_num) (sr 1 413207 619811 (by norm_num) (by norm_num) (sr 1 619811 929717 (by norm_num) (by norm_num) (sr 5 929717 87161 (by norm_num) (by norm_num) (B 87161 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R108831 : Reach 108831 := (sr 1 108831 163247 (by norm_num) (by norm_num) (sr 1 163247 244871 (by norm_num) (by norm_num) (sr 1 244871 367307 (by norm_num) (by norm_num) (sr 1 367307 550961 (by norm_num) (by norm_num) (sr 2 550961 413221 (by norm_num) (by norm_num) (sr 4 413221 77479 (by norm_num) (by norm_num) (B 77479 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108835 : Reach 108835 := (sr 1 108835 163253 (by norm_num) (by norm_num) (sr 5 163253 15305 (by norm_num) (by norm_num) (B 15305 (by norm_num) (by norm_num) (by norm_num))))
theorem R108839 : Reach 108839 := (sr 1 108839 163259 (by norm_num) (by norm_num) (sr 1 163259 244889 (by norm_num) (by norm_num) (sr 2 244889 183667 (by norm_num) (by norm_num) (sr 1 183667 275501 (by norm_num) (by norm_num) (sr 3 275501 103313 (by norm_num) (by norm_num) (sr 2 103313 77485 (by norm_num) (by norm_num) (B 77485 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108843 : Reach 108843 := (sr 1 108843 163265 (by norm_num) (by norm_num) (sr 2 163265 122449 (by norm_num) (by norm_num) (sr 2 122449 91837 (by norm_num) (by norm_num) (B 91837 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108847 : Reach 108847 := (sr 1 108847 163271 (by norm_num) (by norm_num) (sr 1 163271 244907 (by norm_num) (by norm_num) (sr 1 244907 367361 (by norm_num) (by norm_num) (sr 2 367361 275521 (by norm_num) (by norm_num) (sr 2 275521 206641 (by norm_num) (by norm_num) (sr 2 206641 154981 (by norm_num) (by norm_num) (sr 4 154981 29059 (by norm_num) (by norm_num) (B 29059 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R108851 : Reach 108851 := (sr 1 108851 163277 (by norm_num) (by norm_num) (sr 3 163277 61229 (by norm_num) (by norm_num) (B 61229 (by norm_num) (by norm_num) (by norm_num))))
theorem R108855 : Reach 108855 := (sr 1 108855 163283 (by norm_num) (by norm_num) (sr 1 163283 244925 (by norm_num) (by norm_num) (sr 3 244925 91847 (by norm_num) (by norm_num) (B 91847 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108859 : Reach 108859 := (sr 1 108859 163289 (by norm_num) (by norm_num) (sr 2 163289 122467 (by norm_num) (by norm_num) (sr 1 122467 183701 (by norm_num) (by norm_num) (sr 6 183701 8611 (by norm_num) (by norm_num) (B 8611 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108863 : Reach 108863 := (sr 1 108863 163295 (by norm_num) (by norm_num) (sr 1 163295 244943 (by norm_num) (by norm_num) (sr 1 244943 367415 (by norm_num) (by norm_num) (sr 1 367415 551123 (by norm_num) (by norm_num) (sr 1 551123 826685 (by norm_num) (by norm_num) (sr 3 826685 310007 (by norm_num) (by norm_num) (sr 1 310007 465011 (by norm_num) (by norm_num) (sr 1 465011 697517 (by norm_num) (by norm_num) (sr 3 697517 261569 (by norm_num) (by norm_num) (sr 2 261569 196177 (by norm_num) (by norm_num) (sr 2 196177 147133 (by norm_num) (by norm_num) (sr 3 147133 55175 (by norm_num) (by norm_num) (B 55175 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R108867 : Reach 108867 := (sr 1 108867 163301 (by norm_num) (by norm_num) (sr 4 163301 30619 (by norm_num) (by norm_num) (B 30619 (by norm_num) (by norm_num) (by norm_num))))
theorem R108871 : Reach 108871 := (sr 1 108871 163307 (by norm_num) (by norm_num) (sr 1 163307 244961 (by norm_num) (by norm_num) (sr 2 244961 183721 (by norm_num) (by norm_num) (sr 2 183721 137791 (by norm_num) (by norm_num) (sr 1 137791 206687 (by norm_num) (by norm_num) (sr 1 206687 310031 (by norm_num) (by norm_num) (sr 1 310031 465047 (by norm_num) (by norm_num) (sr 1 465047 697571 (by norm_num) (by norm_num) (sr 1 697571 1046357 (by norm_num) (by norm_num) (sr 9 1046357 6131 (by norm_num) (by norm_num) (B 6131 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R108875 : Reach 108875 := (sr 1 108875 163313 (by norm_num) (by norm_num) (sr 2 163313 122485 (by norm_num) (by norm_num) (sr 5 122485 11483 (by norm_num) (by norm_num) (B 11483 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108879 : Reach 108879 := (sr 1 108879 163319 (by norm_num) (by norm_num) (sr 1 163319 244979 (by norm_num) (by norm_num) (sr 1 244979 367469 (by norm_num) (by norm_num) (sr 3 367469 137801 (by norm_num) (by norm_num) (sr 2 137801 103351 (by norm_num) (by norm_num) R103351)))))
theorem R108883 : Reach 108883 := (sr 1 108883 163325 (by norm_num) (by norm_num) (sr 3 163325 61247 (by norm_num) (by norm_num) (B 61247 (by norm_num) (by norm_num) (by norm_num))))
theorem R108887 : Reach 108887 := (sr 1 108887 163331 (by norm_num) (by norm_num) (sr 1 163331 244997 (by norm_num) (by norm_num) (sr 4 244997 45937 (by norm_num) (by norm_num) (B 45937 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108891 : Reach 108891 := (sr 1 108891 163337 (by norm_num) (by norm_num) (sr 2 163337 122503 (by norm_num) (by norm_num) (sr 1 122503 183755 (by norm_num) (by norm_num) (sr 1 183755 275633 (by norm_num) (by norm_num) (sr 2 275633 206725 (by norm_num) (by norm_num) (sr 4 206725 38761 (by norm_num) (by norm_num) (B 38761 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108895 : Reach 108895 := (sr 1 108895 163343 (by norm_num) (by norm_num) (sr 1 163343 245015 (by norm_num) (by norm_num) (sr 1 245015 367523 (by norm_num) (by norm_num) (sr 1 367523 551285 (by norm_num) (by norm_num) (sr 5 551285 51683 (by norm_num) (by norm_num) (B 51683 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R108899 : Reach 108899 := (sr 1 108899 163349 (by norm_num) (by norm_num) (sr 6 163349 7657 (by norm_num) (by norm_num) (B 7657 (by norm_num) (by norm_num) (by norm_num))))
theorem R108903 : Reach 108903 := (sr 1 108903 163355 (by norm_num) (by norm_num) (sr 1 163355 245033 (by norm_num) (by norm_num) (sr 2 245033 183775 (by norm_num) (by norm_num) (sr 1 183775 275663 (by norm_num) (by norm_num) (sr 1 275663 413495 (by norm_num) (by norm_num) (sr 1 413495 620243 (by norm_num) (by norm_num) (sr 1 620243 930365 (by norm_num) (by norm_num) (sr 3 930365 348887 (by norm_num) (by norm_num) (sr 1 348887 523331 (by norm_num) (by norm_num) (sr 1 523331 784997 (by norm_num) (by norm_num) (sr 4 784997 147187 (by norm_num) (by norm_num) (sr 1 147187 220781 (by norm_num) (by norm_num) (sr 3 220781 82793 (by norm_num) (by norm_num) (B 82793 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R108907 : Reach 108907 := (sr 1 108907 163361 (by norm_num) (by norm_num) (sr 2 163361 122521 (by norm_num) (by norm_num) (sr 2 122521 91891 (by norm_num) (by norm_num) (B 91891 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108911 : Reach 108911 := (sr 1 108911 163367 (by norm_num) (by norm_num) (sr 1 163367 245051 (by norm_num) (by norm_num) (sr 1 245051 367577 (by norm_num) (by norm_num) (sr 2 367577 275683 (by norm_num) (by norm_num) (sr 1 275683 413525 (by norm_num) (by norm_num) (sr 9 413525 2423 (by norm_num) (by norm_num) (B 2423 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108915 : Reach 108915 := (sr 1 108915 163373 (by norm_num) (by norm_num) (sr 3 163373 61265 (by norm_num) (by norm_num) (B 61265 (by norm_num) (by norm_num) (by norm_num))))
theorem R108919 : Reach 108919 := (sr 1 108919 163379 (by norm_num) (by norm_num) (sr 1 163379 245069 (by norm_num) (by norm_num) (sr 3 245069 91901 (by norm_num) (by norm_num) (B 91901 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108923 : Reach 108923 := (sr 1 108923 163385 (by norm_num) (by norm_num) (sr 2 163385 122539 (by norm_num) (by norm_num) (sr 1 122539 183809 (by norm_num) (by norm_num) (sr 2 183809 137857 (by norm_num) (by norm_num) (sr 2 137857 103393 (by norm_num) (by norm_num) (sr 2 103393 77545 (by norm_num) (by norm_num) (B 77545 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108927 : Reach 108927 := (sr 1 108927 163391 (by norm_num) (by norm_num) (sr 1 163391 245087 (by norm_num) (by norm_num) (sr 1 245087 367631 (by norm_num) (by norm_num) (sr 1 367631 551447 (by norm_num) (by norm_num) (sr 1 551447 827171 (by norm_num) (by norm_num) (sr 1 827171 1240757 (by norm_num) (by norm_num) (sr 5 1240757 116321 (by norm_num) (by norm_num) (sr 2 116321 87241 (by norm_num) (by norm_num) (B 87241 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R108931 : Reach 108931 := (sr 1 108931 163397 (by norm_num) (by norm_num) (sr 4 163397 30637 (by norm_num) (by norm_num) (B 30637 (by norm_num) (by norm_num) (by norm_num))))
theorem R108935 : Reach 108935 := (sr 1 108935 163403 (by norm_num) (by norm_num) (sr 1 163403 245105 (by norm_num) (by norm_num) (sr 2 245105 183829 (by norm_num) (by norm_num) (sr 6 183829 8617 (by norm_num) (by norm_num) (B 8617 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108939 : Reach 108939 := (sr 1 108939 163409 (by norm_num) (by norm_num) (sr 2 163409 122557 (by norm_num) (by norm_num) (sr 3 122557 45959 (by norm_num) (by norm_num) (B 45959 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108943 : Reach 108943 := (sr 1 108943 163415 (by norm_num) (by norm_num) (sr 1 163415 245123 (by norm_num) (by norm_num) (sr 1 245123 367685 (by norm_num) (by norm_num) (sr 4 367685 68941 (by norm_num) (by norm_num) (B 68941 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108947 : Reach 108947 := (sr 1 108947 163421 (by norm_num) (by norm_num) (sr 3 163421 61283 (by norm_num) (by norm_num) (B 61283 (by norm_num) (by norm_num) (by norm_num))))
theorem R108951 : Reach 108951 := (sr 1 108951 163427 (by norm_num) (by norm_num) (sr 1 163427 245141 (by norm_num) (by norm_num) (sr 6 245141 11491 (by norm_num) (by norm_num) (B 11491 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108955 : Reach 108955 := (sr 1 108955 163433 (by norm_num) (by norm_num) (sr 2 163433 122575 (by norm_num) (by norm_num) (sr 1 122575 183863 (by norm_num) (by norm_num) (sr 1 183863 275795 (by norm_num) (by norm_num) (sr 1 275795 413693 (by norm_num) (by norm_num) (sr 3 413693 155135 (by norm_num) (by norm_num) (sr 1 155135 232703 (by norm_num) (by norm_num) (sr 1 232703 349055 (by norm_num) (by norm_num) (sr 1 349055 523583 (by norm_num) (by norm_num) (sr 1 523583 785375 (by norm_num) (by norm_num) (sr 1 785375 1178063 (by norm_num) (by norm_num) (sr 1 1178063 1767095 (by norm_num) (by norm_num) (sr 1 1767095 2650643 (by norm_num) (by norm_num) (sr 1 2650643 3975965 (by norm_num) (by norm_num) (sr 3 3975965 1490987 (by norm_num) (by norm_num) (sr 1 1490987 2236481 (by norm_num) (by norm_num) (sr 2 2236481 1677361 (by norm_num) (by norm_num) (sr 2 1677361 1258021 (by norm_num) (by norm_num) (sr 4 1258021 235879 (by norm_num) (by norm_num) (sr 1 235879 353819 (by norm_num) (by norm_num) (sr 1 353819 530729 (by norm_num) (by norm_num) (sr 2 530729 398047 (by norm_num) (by norm_num) (sr 1 398047 597071 (by norm_num) (by norm_num) (sr 1 597071 895607 (by norm_num) (by norm_num) (sr 1 895607 1343411 (by norm_num) (by norm_num) (sr 1 1343411 2015117 (by norm_num) (by norm_num) (sr 3 2015117 755669 (by norm_num) (by norm_num) (sr 7 755669 17711 (by norm_num) (by norm_num) (B 17711 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))
theorem R108959 : Reach 108959 := (sr 1 108959 163439 (by norm_num) (by norm_num) (sr 1 163439 245159 (by norm_num) (by norm_num) (sr 1 245159 367739 (by norm_num) (by norm_num) (sr 1 367739 551609 (by norm_num) (by norm_num) (sr 2 551609 413707 (by norm_num) (by norm_num) (sr 1 413707 620561 (by norm_num) (by norm_num) (sr 2 620561 465421 (by norm_num) (by norm_num) (sr 3 465421 174533 (by norm_num) (by norm_num) (sr 4 174533 32725 (by norm_num) (by norm_num) (B 32725 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R108963 : Reach 108963 := (sr 1 108963 163445 (by norm_num) (by norm_num) (sr 5 163445 15323 (by norm_num) (by norm_num) (B 15323 (by norm_num) (by norm_num) (by norm_num))))
theorem R108967 : Reach 108967 := (sr 1 108967 163451 (by norm_num) (by norm_num) (sr 1 163451 245177 (by norm_num) (by norm_num) (sr 2 245177 183883 (by norm_num) (by norm_num) (sr 1 183883 275825 (by norm_num) (by norm_num) (sr 2 275825 206869 (by norm_num) (by norm_num) (sr 6 206869 9697 (by norm_num) (by norm_num) (B 9697 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R108971 : Reach 108971 := (sr 1 108971 163457 (by norm_num) (by norm_num) (sr 2 163457 122593 (by norm_num) (by norm_num) (sr 2 122593 91945 (by norm_num) (by norm_num) (B 91945 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108975 : Reach 108975 := (sr 1 108975 163463 (by norm_num) (by norm_num) (sr 1 163463 245195 (by norm_num) (by norm_num) (sr 1 245195 367793 (by norm_num) (by norm_num) (sr 2 367793 275845 (by norm_num) (by norm_num) (sr 4 275845 51721 (by norm_num) (by norm_num) (B 51721 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R108979 : Reach 108979 := (sr 1 108979 163469 (by norm_num) (by norm_num) (sr 3 163469 61301 (by norm_num) (by norm_num) (B 61301 (by norm_num) (by norm_num) (by norm_num))))
theorem R108983 : Reach 108983 := (sr 1 108983 163475 (by norm_num) (by norm_num) (sr 1 163475 245213 (by norm_num) (by norm_num) (sr 3 245213 91955 (by norm_num) (by norm_num) (B 91955 (by norm_num) (by norm_num) (by norm_num)))))
theorem R108987 : Reach 108987 := (sr 1 108987 163481 (by norm_num) (by norm_num) (sr 2 163481 122611 (by norm_num) (by norm_num) (sr 1 122611 183917 (by norm_num) (by norm_num) (sr 3 183917 68969 (by norm_num) (by norm_num) (B 68969 (by norm_num) (by norm_num) (by norm_num))))))
theorem R108991 : Reach 108991 := (sr 1 108991 163487 (by norm_num) (by norm_num) (sr 1 163487 245231 (by norm_num) (by norm_num) (sr 1 245231 367847 (by norm_num) (by norm_num) (sr 1 367847 551771 (by norm_num) (by norm_num) (sr 1 551771 827657 (by norm_num) (by norm_num) (sr 2 827657 620743 (by norm_num) (by norm_num) (sr 1 620743 931115 (by norm_num) (by norm_num) (sr 1 931115 1396673 (by norm_num) (by norm_num) (sr 2 1396673 1047505 (by norm_num) (by norm_num) (sr 2 1047505 785629 (by norm_num) (by norm_num) (sr 3 785629 294611 (by norm_num) (by norm_num) (sr 1 294611 441917 (by norm_num) (by norm_num) (sr 3 441917 165719 (by norm_num) (by norm_num) (sr 1 165719 248579 (by norm_num) (by norm_num) (sr 1 248579 372869 (by norm_num) (by norm_num) (sr 4 372869 69913 (by norm_num) (by norm_num) (B 69913 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))
theorem R108995 : Reach 108995 := (sr 1 108995 163493 (by norm_num) (by norm_num) (sr 4 163493 30655 (by norm_num) (by norm_num) (B 30655 (by norm_num) (by norm_num) (by norm_num))))
theorem R108999 : Reach 108999 := (sr 1 108999 163499 (by norm_num) (by norm_num) (sr 1 163499 245249 (by norm_num) (by norm_num) (sr 2 245249 183937 (by norm_num) (by norm_num) (sr 2 183937 137953 (by norm_num) (by norm_num) (sr 2 137953 103465 (by norm_num) (by norm_num) (sr 2 103465 77599 (by norm_num) (by norm_num) (B 77599 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R109003 : Reach 109003 := (sr 1 109003 163505 (by norm_num) (by norm_num) (sr 2 163505 122629 (by norm_num) (by norm_num) (sr 4 122629 22993 (by norm_num) (by norm_num) (B 22993 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109007 : Reach 109007 := (sr 1 109007 163511 (by norm_num) (by norm_num) (sr 1 163511 245267 (by norm_num) (by norm_num) (sr 1 245267 367901 (by norm_num) (by norm_num) (sr 3 367901 137963 (by norm_num) (by norm_num) (sr 1 137963 206945 (by norm_num) (by norm_num) (sr 2 206945 155209 (by norm_num) (by norm_num) (sr 2 155209 116407 (by norm_num) (by norm_num) (sr 1 116407 174611 (by norm_num) (by norm_num) (sr 1 174611 261917 (by norm_num) (by norm_num) (sr 3 261917 98219 (by norm_num) (by norm_num) (B 98219 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R109011 : Reach 109011 := (sr 1 109011 163517 (by norm_num) (by norm_num) (sr 3 163517 61319 (by norm_num) (by norm_num) (B 61319 (by norm_num) (by norm_num) (by norm_num))))
theorem R109015 : Reach 109015 := (sr 1 109015 163523 (by norm_num) (by norm_num) (sr 1 163523 245285 (by norm_num) (by norm_num) (sr 4 245285 45991 (by norm_num) (by norm_num) (B 45991 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109019 : Reach 109019 := (sr 1 109019 163529 (by norm_num) (by norm_num) (sr 2 163529 122647 (by norm_num) (by norm_num) (sr 1 122647 183971 (by norm_num) (by norm_num) (sr 1 183971 275957 (by norm_num) (by norm_num) (sr 5 275957 25871 (by norm_num) (by norm_num) (B 25871 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R109023 : Reach 109023 := (sr 1 109023 163535 (by norm_num) (by norm_num) (sr 1 163535 245303 (by norm_num) (by norm_num) (sr 1 245303 367955 (by norm_num) (by norm_num) (sr 1 367955 551933 (by norm_num) (by norm_num) (sr 3 551933 206975 (by norm_num) (by norm_num) (sr 1 206975 310463 (by norm_num) (by norm_num) (sr 1 310463 465695 (by norm_num) (by norm_num) (sr 1 465695 698543 (by norm_num) (by norm_num) (sr 1 698543 1047815 (by norm_num) (by norm_num) (sr 1 1047815 1571723 (by norm_num) (by norm_num) (sr 1 1571723 2357585 (by norm_num) (by norm_num) (sr 2 2357585 1768189 (by norm_num) (by norm_num) (sr 3 1768189 663071 (by norm_num) (by norm_num) (sr 1 663071 994607 (by norm_num) (by norm_num) (sr 1 994607 1491911 (by norm_num) (by norm_num) (sr 1 1491911 2237867 (by norm_num) (by norm_num) (sr 1 2237867 3356801 (by norm_num) (by norm_num) (sr 2 3356801 2517601 (by norm_num) (by norm_num) (sr 2 2517601 1888201 (by norm_num) (by norm_num) (sr 2 1888201 1416151 (by norm_num) (by norm_num) (sr 1 1416151 2124227 (by norm_num) (by norm_num) (sr 1 2124227 3186341 (by norm_num) (by norm_num) (sr 4 3186341 597439 (by norm_num) (by norm_num) (sr 1 597439 896159 (by norm_num) (by norm_num) (sr 1 896159 1344239 (by norm_num) (by norm_num) (sr 1 1344239 2016359 (by norm_num) (by norm_num) (sr 1 2016359 3024539 (by norm_num) (by norm_num) (sr 1 3024539 4536809 (by norm_num) (by norm_num) (sr 2 4536809 3402607 (by norm_num) (by norm_num) (sr 1 3402607 5103911 (by norm_num) (by norm_num) (sr 1 5103911 7655867 (by norm_num) (by norm_num) (sr 1 7655867 11483801 (by norm_num) (by norm_num) (sr 2 11483801 8612851 (by norm_num) (by norm_num) (sr 1 8612851 12919277 (by norm_num) (by norm_num) (sr 3 12919277 4844729 (by norm_num) (by norm_num) (sr 2 4844729 3633547 (by norm_num) (by norm_num) (sr 1 3633547 5450321 (by norm_num) (by norm_num) (sr 2 5450321 4087741 (by norm_num) (by norm_num) (sr 3 4087741 1532903 (by norm_num) (by norm_num) (sr 1 1532903 2299355 (by norm_num) (by norm_num) (sr 1 2299355 3449033 (by norm_num) (by norm_num) (sr 2 3449033 2586775 (by norm_num) (by norm_num) (sr 1 2586775 3880163 (by norm_num) (by norm_num) (sr 1 3880163 5820245 (by norm_num) (by norm_num) (sr 9 5820245 34103 (by norm_num) (by norm_num) (B 34103 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))))))))))))))))))))))
theorem R109027 : Reach 109027 := (sr 1 109027 163541 (by norm_num) (by norm_num) (sr 7 163541 3833 (by norm_num) (by norm_num) (B 3833 (by norm_num) (by norm_num) (by norm_num))))
theorem R109031 : Reach 109031 := (sr 1 109031 163547 (by norm_num) (by norm_num) (sr 1 163547 245321 (by norm_num) (by norm_num) (sr 2 245321 183991 (by norm_num) (by norm_num) (sr 1 183991 275987 (by norm_num) (by norm_num) (sr 1 275987 413981 (by norm_num) (by norm_num) (sr 3 413981 155243 (by norm_num) (by norm_num) (sr 1 155243 232865 (by norm_num) (by norm_num) (sr 2 232865 174649 (by norm_num) (by norm_num) (sr 2 174649 130987 (by norm_num) (by norm_num) (sr 1 130987 196481 (by norm_num) (by norm_num) (sr 2 196481 147361 (by norm_num) (by norm_num) (sr 2 147361 110521 (by norm_num) (by norm_num) (sr 2 110521 82891 (by norm_num) (by norm_num) (B 82891 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R109035 : Reach 109035 := (sr 1 109035 163553 (by norm_num) (by norm_num) (sr 2 163553 122665 (by norm_num) (by norm_num) (sr 2 122665 91999 (by norm_num) (by norm_num) (B 91999 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109039 : Reach 109039 := (sr 1 109039 163559 (by norm_num) (by norm_num) (sr 1 163559 245339 (by norm_num) (by norm_num) (sr 1 245339 368009 (by norm_num) (by norm_num) (sr 2 368009 276007 (by norm_num) (by norm_num) (sr 1 276007 414011 (by norm_num) (by norm_num) (sr 1 414011 621017 (by norm_num) (by norm_num) (sr 2 621017 465763 (by norm_num) (by norm_num) (sr 1 465763 698645 (by norm_num) (by norm_num) (sr 6 698645 32749 (by norm_num) (by norm_num) (B 32749 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R109043 : Reach 109043 := (sr 1 109043 163565 (by norm_num) (by norm_num) (sr 3 163565 61337 (by norm_num) (by norm_num) (B 61337 (by norm_num) (by norm_num) (by norm_num))))
theorem R109047 : Reach 109047 := (sr 1 109047 163571 (by norm_num) (by norm_num) (sr 1 163571 245357 (by norm_num) (by norm_num) (sr 3 245357 92009 (by norm_num) (by norm_num) (B 92009 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109051 : Reach 109051 := (sr 1 109051 163577 (by norm_num) (by norm_num) (sr 2 163577 122683 (by norm_num) (by norm_num) (sr 1 122683 184025 (by norm_num) (by norm_num) (sr 2 184025 138019 (by norm_num) (by norm_num) (sr 1 138019 207029 (by norm_num) (by norm_num) (sr 5 207029 19409 (by norm_num) (by norm_num) (B 19409 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R109055 : Reach 109055 := (sr 1 109055 163583 (by norm_num) (by norm_num) (sr 1 163583 245375 (by norm_num) (by norm_num) (sr 1 245375 368063 (by norm_num) (by norm_num) (sr 1 368063 552095 (by norm_num) (by norm_num) (sr 1 552095 828143 (by norm_num) (by norm_num) (sr 1 828143 1242215 (by norm_num) (by norm_num) (sr 1 1242215 1863323 (by norm_num) (by norm_num) (sr 1 1863323 2794985 (by norm_num) (by norm_num) (sr 2 2794985 2096239 (by norm_num) (by norm_num) (sr 1 2096239 3144359 (by norm_num) (by norm_num) (sr 1 3144359 4716539 (by norm_num) (by norm_num) (sr 1 4716539 7074809 (by norm_num) (by norm_num) (sr 2 7074809 5306107 (by norm_num) (by norm_num) (sr 1 5306107 7959161 (by norm_num) (by norm_num) (sr 2 7959161 5969371 (by norm_num) (by norm_num) (sr 1 5969371 8954057 (by norm_num) (by norm_num) (sr 2 8954057 6715543 (by norm_num) (by norm_num) (sr 1 6715543 10073315 (by norm_num) (by norm_num) (sr 1 10073315 15109973 (by norm_num) (by norm_num) (sr 9 15109973 88535 (by norm_num) (by norm_num) (B 88535 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))
theorem R109059 : Reach 109059 := (sr 1 109059 163589 (by norm_num) (by norm_num) (sr 4 163589 30673 (by norm_num) (by norm_num) (B 30673 (by norm_num) (by norm_num) (by norm_num))))
theorem R109063 : Reach 109063 := (sr 1 109063 163595 (by norm_num) (by norm_num) (sr 1 163595 245393 (by norm_num) (by norm_num) (sr 2 245393 184045 (by norm_num) (by norm_num) (sr 3 184045 69017 (by norm_num) (by norm_num) (B 69017 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109067 : Reach 109067 := (sr 1 109067 163601 (by norm_num) (by norm_num) (sr 2 163601 122701 (by norm_num) (by norm_num) (sr 3 122701 46013 (by norm_num) (by norm_num) (B 46013 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109071 : Reach 109071 := (sr 1 109071 163607 (by norm_num) (by norm_num) (sr 1 163607 245411 (by norm_num) (by norm_num) (sr 1 245411 368117 (by norm_num) (by norm_num) (sr 5 368117 34511 (by norm_num) (by norm_num) (B 34511 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109075 : Reach 109075 := (sr 1 109075 163613 (by norm_num) (by norm_num) (sr 3 163613 61355 (by norm_num) (by norm_num) (B 61355 (by norm_num) (by norm_num) (by norm_num))))
theorem R109079 : Reach 109079 := (sr 1 109079 163619 (by norm_num) (by norm_num) (sr 1 163619 245429 (by norm_num) (by norm_num) (sr 5 245429 23009 (by norm_num) (by norm_num) (B 23009 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109083 : Reach 109083 := (sr 1 109083 163625 (by norm_num) (by norm_num) (sr 2 163625 122719 (by norm_num) (by norm_num) (sr 1 122719 184079 (by norm_num) (by norm_num) (sr 1 184079 276119 (by norm_num) (by norm_num) (sr 1 276119 414179 (by norm_num) (by norm_num) (sr 1 414179 621269 (by norm_num) (by norm_num) (sr 7 621269 14561 (by norm_num) (by norm_num) (B 14561 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R109087 : Reach 109087 := (sr 1 109087 163631 (by norm_num) (by norm_num) (sr 1 163631 245447 (by norm_num) (by norm_num) (sr 1 245447 368171 (by norm_num) (by norm_num) (sr 1 368171 552257 (by norm_num) (by norm_num) (sr 2 552257 414193 (by norm_num) (by norm_num) (sr 2 414193 310645 (by norm_num) (by norm_num) (sr 5 310645 29123 (by norm_num) (by norm_num) (B 29123 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R109091 : Reach 109091 := (sr 1 109091 163637 (by norm_num) (by norm_num) (sr 5 163637 15341 (by norm_num) (by norm_num) (B 15341 (by norm_num) (by norm_num) (by norm_num))))
theorem R109095 : Reach 109095 := (sr 1 109095 163643 (by norm_num) (by norm_num) (sr 1 163643 245465 (by norm_num) (by norm_num) (sr 2 245465 184099 (by norm_num) (by norm_num) (sr 1 184099 276149 (by norm_num) (by norm_num) (sr 5 276149 25889 (by norm_num) (by norm_num) (B 25889 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R109099 : Reach 109099 := (sr 1 109099 163649 (by norm_num) (by norm_num) (sr 2 163649 122737 (by norm_num) (by norm_num) (sr 2 122737 92053 (by norm_num) (by norm_num) (B 92053 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109103 : Reach 109103 := (sr 1 109103 163655 (by norm_num) (by norm_num) (sr 1 163655 245483 (by norm_num) (by norm_num) (sr 1 245483 368225 (by norm_num) (by norm_num) (sr 2 368225 276169 (by norm_num) (by norm_num) (sr 2 276169 207127 (by norm_num) (by norm_num) (sr 1 207127 310691 (by norm_num) (by norm_num) (sr 1 310691 466037 (by norm_num) (by norm_num) (sr 5 466037 43691 (by norm_num) (by norm_num) (B 43691 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R109107 : Reach 109107 := (sr 1 109107 163661 (by norm_num) (by norm_num) (sr 3 163661 61373 (by norm_num) (by norm_num) (B 61373 (by norm_num) (by norm_num) (by norm_num))))
theorem R109111 : Reach 109111 := (sr 1 109111 163667 (by norm_num) (by norm_num) (sr 1 163667 245501 (by norm_num) (by norm_num) (sr 3 245501 92063 (by norm_num) (by norm_num) (B 92063 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109115 : Reach 109115 := (sr 1 109115 163673 (by norm_num) (by norm_num) (sr 2 163673 122755 (by norm_num) (by norm_num) (sr 1 122755 184133 (by norm_num) (by norm_num) (sr 4 184133 34525 (by norm_num) (by norm_num) (B 34525 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109119 : Reach 109119 := (sr 1 109119 163679 (by norm_num) (by norm_num) (sr 1 163679 245519 (by norm_num) (by norm_num) (sr 1 245519 368279 (by norm_num) (by norm_num) (sr 1 368279 552419 (by norm_num) (by norm_num) (sr 1 552419 828629 (by norm_num) (by norm_num) (sr 7 828629 19421 (by norm_num) (by norm_num) (B 19421 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R109123 : Reach 109123 := (sr 1 109123 163685 (by norm_num) (by norm_num) (sr 4 163685 30691 (by norm_num) (by norm_num) (B 30691 (by norm_num) (by norm_num) (by norm_num))))
theorem R109127 : Reach 109127 := (sr 1 109127 163691 (by norm_num) (by norm_num) (sr 1 163691 245537 (by norm_num) (by norm_num) (sr 2 245537 184153 (by norm_num) (by norm_num) (sr 2 184153 138115 (by norm_num) (by norm_num) (sr 1 138115 207173 (by norm_num) (by norm_num) (sr 4 207173 38845 (by norm_num) (by norm_num) (B 38845 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R109131 : Reach 109131 := (sr 1 109131 163697 (by norm_num) (by norm_num) (sr 2 163697 122773 (by norm_num) (by norm_num) (sr 6 122773 5755 (by norm_num) (by norm_num) (B 5755 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109135 : Reach 109135 := (sr 1 109135 163703 (by norm_num) (by norm_num) (sr 1 163703 245555 (by norm_num) (by norm_num) (sr 1 245555 368333 (by norm_num) (by norm_num) (sr 3 368333 138125 (by norm_num) (by norm_num) (sr 3 138125 51797 (by norm_num) (by norm_num) (B 51797 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R109139 : Reach 109139 := (sr 1 109139 163709 (by norm_num) (by norm_num) (sr 3 163709 61391 (by norm_num) (by norm_num) (B 61391 (by norm_num) (by norm_num) (by norm_num))))
theorem R109143 : Reach 109143 := (sr 1 109143 163715 (by norm_num) (by norm_num) (sr 1 163715 245573 (by norm_num) (by norm_num) (sr 4 245573 46045 (by norm_num) (by norm_num) (B 46045 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109147 : Reach 109147 := (sr 1 109147 163721 (by norm_num) (by norm_num) (sr 2 163721 122791 (by norm_num) (by norm_num) (sr 1 122791 184187 (by norm_num) (by norm_num) (sr 1 184187 276281 (by norm_num) (by norm_num) (sr 2 276281 207211 (by norm_num) (by norm_num) (sr 1 207211 310817 (by norm_num) (by norm_num) (sr 2 310817 233113 (by norm_num) (by norm_num) (sr 2 233113 174835 (by norm_num) (by norm_num) (sr 1 174835 262253 (by norm_num) (by norm_num) (sr 3 262253 98345 (by norm_num) (by norm_num) (B 98345 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R109151 : Reach 109151 := (sr 1 109151 163727 (by norm_num) (by norm_num) (sr 1 163727 245591 (by norm_num) (by norm_num) (sr 1 245591 368387 (by norm_num) (by norm_num) (sr 1 368387 552581 (by norm_num) (by norm_num) (sr 4 552581 103609 (by norm_num) (by norm_num) (sr 2 103609 77707 (by norm_num) (by norm_num) (B 77707 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R109155 : Reach 109155 := (sr 1 109155 163733 (by norm_num) (by norm_num) (sr 6 163733 7675 (by norm_num) (by norm_num) (B 7675 (by norm_num) (by norm_num) (by norm_num))))
theorem R109159 : Reach 109159 := (sr 1 109159 163739 (by norm_num) (by norm_num) (sr 1 163739 245609 (by norm_num) (by norm_num) (sr 2 245609 184207 (by norm_num) (by norm_num) (sr 1 184207 276311 (by norm_num) (by norm_num) (sr 1 276311 414467 (by norm_num) (by norm_num) (sr 1 414467 621701 (by norm_num) (by norm_num) (sr 4 621701 116569 (by norm_num) (by norm_num) (sr 2 116569 87427 (by norm_num) (by norm_num) (B 87427 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R109163 : Reach 109163 := (sr 1 109163 163745 (by norm_num) (by norm_num) (sr 2 163745 122809 (by norm_num) (by norm_num) (sr 2 122809 92107 (by norm_num) (by norm_num) (B 92107 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109167 : Reach 109167 := (sr 1 109167 163751 (by norm_num) (by norm_num) (sr 1 163751 245627 (by norm_num) (by norm_num) (sr 1 245627 368441 (by norm_num) (by norm_num) (sr 2 368441 276331 (by norm_num) (by norm_num) (sr 1 276331 414497 (by norm_num) (by norm_num) (sr 2 414497 310873 (by norm_num) (by norm_num) (sr 2 310873 233155 (by norm_num) (by norm_num) (sr 1 233155 349733 (by norm_num) (by norm_num) (sr 4 349733 65575 (by norm_num) (by norm_num) (B 65575 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R109171 : Reach 109171 := (sr 1 109171 163757 (by norm_num) (by norm_num) (sr 3 163757 61409 (by norm_num) (by norm_num) (B 61409 (by norm_num) (by norm_num) (by norm_num))))
theorem R109175 : Reach 109175 := (sr 1 109175 163763 (by norm_num) (by norm_num) (sr 1 163763 245645 (by norm_num) (by norm_num) (sr 3 245645 92117 (by norm_num) (by norm_num) (B 92117 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109179 : Reach 109179 := (sr 1 109179 163769 (by norm_num) (by norm_num) (sr 2 163769 122827 (by norm_num) (by norm_num) (sr 1 122827 184241 (by norm_num) (by norm_num) (sr 2 184241 138181 (by norm_num) (by norm_num) (sr 4 138181 25909 (by norm_num) (by norm_num) (B 25909 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R109183 : Reach 109183 := (sr 1 109183 163775 (by norm_num) (by norm_num) (sr 1 163775 245663 (by norm_num) (by norm_num) (sr 1 245663 368495 (by norm_num) (by norm_num) (sr 1 368495 552743 (by norm_num) (by norm_num) (sr 1 552743 829115 (by norm_num) (by norm_num) (sr 1 829115 1243673 (by norm_num) (by norm_num) (sr 2 1243673 932755 (by norm_num) (by norm_num) (sr 1 932755 1399133 (by norm_num) (by norm_num) (sr 3 1399133 524675 (by norm_num) (by norm_num) (sr 1 524675 787013 (by norm_num) (by norm_num) (sr 4 787013 147565 (by norm_num) (by norm_num) (sr 3 147565 55337 (by norm_num) (by norm_num) (B 55337 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R109187 : Reach 109187 := (sr 1 109187 163781 (by norm_num) (by norm_num) (sr 4 163781 30709 (by norm_num) (by norm_num) (B 30709 (by norm_num) (by norm_num) (by norm_num))))
theorem R109191 : Reach 109191 := (sr 1 109191 163787 (by norm_num) (by norm_num) (sr 1 163787 245681 (by norm_num) (by norm_num) (sr 2 245681 184261 (by norm_num) (by norm_num) (sr 4 184261 34549 (by norm_num) (by norm_num) (B 34549 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109195 : Reach 109195 := (sr 1 109195 163793 (by norm_num) (by norm_num) (sr 2 163793 122845 (by norm_num) (by norm_num) (sr 3 122845 46067 (by norm_num) (by norm_num) (B 46067 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109199 : Reach 109199 := (sr 1 109199 163799 (by norm_num) (by norm_num) (sr 1 163799 245699 (by norm_num) (by norm_num) (sr 1 245699 368549 (by norm_num) (by norm_num) (sr 4 368549 69103 (by norm_num) (by norm_num) (B 69103 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109203 : Reach 109203 := (sr 1 109203 163805 (by norm_num) (by norm_num) (sr 3 163805 61427 (by norm_num) (by norm_num) (B 61427 (by norm_num) (by norm_num) (by norm_num))))
theorem R109207 : Reach 109207 := (sr 1 109207 163811 (by norm_num) (by norm_num) (sr 1 163811 245717 (by norm_num) (by norm_num) (sr 7 245717 5759 (by norm_num) (by norm_num) (B 5759 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109211 : Reach 109211 := (sr 1 109211 163817 (by norm_num) (by norm_num) (sr 2 163817 122863 (by norm_num) (by norm_num) (sr 1 122863 184295 (by norm_num) (by norm_num) (sr 1 184295 276443 (by norm_num) (by norm_num) (sr 1 276443 414665 (by norm_num) (by norm_num) (sr 2 414665 310999 (by norm_num) (by norm_num) (sr 1 310999 466499 (by norm_num) (by norm_num) (sr 1 466499 699749 (by norm_num) (by norm_num) (sr 4 699749 131203 (by norm_num) (by norm_num) (sr 1 131203 196805 (by norm_num) (by norm_num) (sr 4 196805 36901 (by norm_num) (by norm_num) (B 36901 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R109215 : Reach 109215 := (sr 1 109215 163823 (by norm_num) (by norm_num) (sr 1 163823 245735 (by norm_num) (by norm_num) (sr 1 245735 368603 (by norm_num) (by norm_num) (sr 1 368603 552905 (by norm_num) (by norm_num) (sr 2 552905 414679 (by norm_num) (by norm_num) (sr 1 414679 622019 (by norm_num) (by norm_num) (sr 1 622019 933029 (by norm_num) (by norm_num) (sr 4 933029 174943 (by norm_num) (by norm_num) (sr 1 174943 262415 (by norm_num) (by norm_num) (sr 1 262415 393623 (by norm_num) (by norm_num) (sr 1 393623 590435 (by norm_num) (by norm_num) (sr 1 590435 885653 (by norm_num) (by norm_num) (sr 6 885653 41515 (by norm_num) (by norm_num) (B 41515 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R109219 : Reach 109219 := (sr 1 109219 163829 (by norm_num) (by norm_num) (sr 5 163829 15359 (by norm_num) (by norm_num) (B 15359 (by norm_num) (by norm_num) (by norm_num))))
theorem R109223 : Reach 109223 := (sr 1 109223 163835 (by norm_num) (by norm_num) (sr 1 163835 245753 (by norm_num) (by norm_num) (sr 2 245753 184315 (by norm_num) (by norm_num) (sr 1 184315 276473 (by norm_num) (by norm_num) (sr 2 276473 207355 (by norm_num) (by norm_num) (sr 1 207355 311033 (by norm_num) (by norm_num) (sr 2 311033 233275 (by norm_num) (by norm_num) (sr 1 233275 349913 (by norm_num) (by norm_num) (sr 2 349913 262435 (by norm_num) (by norm_num) (sr 1 262435 393653 (by norm_num) (by norm_num) (sr 5 393653 36905 (by norm_num) (by norm_num) (B 36905 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R109227 : Reach 109227 := (sr 1 109227 163841 (by norm_num) (by norm_num) (sr 2 163841 122881 (by norm_num) (by norm_num) (sr 2 122881 92161 (by norm_num) (by norm_num) (B 92161 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109231 : Reach 109231 := (sr 1 109231 163847 (by norm_num) (by norm_num) (sr 1 163847 245771 (by norm_num) (by norm_num) (sr 1 245771 368657 (by norm_num) (by norm_num) (sr 2 368657 276493 (by norm_num) (by norm_num) (sr 3 276493 103685 (by norm_num) (by norm_num) (sr 4 103685 19441 (by norm_num) (by norm_num) (B 19441 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R109235 : Reach 109235 := (sr 1 109235 163853 (by norm_num) (by norm_num) (sr 3 163853 61445 (by norm_num) (by norm_num) (B 61445 (by norm_num) (by norm_num) (by norm_num))))
theorem R109239 : Reach 109239 := (sr 1 109239 163859 (by norm_num) (by norm_num) (sr 1 163859 245789 (by norm_num) (by norm_num) (sr 3 245789 92171 (by norm_num) (by norm_num) (B 92171 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109243 : Reach 109243 := (sr 1 109243 163865 (by norm_num) (by norm_num) (sr 2 163865 122899 (by norm_num) (by norm_num) (sr 1 122899 184349 (by norm_num) (by norm_num) (sr 3 184349 69131 (by norm_num) (by norm_num) (B 69131 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109247 : Reach 109247 := (sr 1 109247 163871 (by norm_num) (by norm_num) (sr 1 163871 245807 (by norm_num) (by norm_num) (sr 1 245807 368711 (by norm_num) (by norm_num) (sr 1 368711 553067 (by norm_num) (by norm_num) (sr 1 553067 829601 (by norm_num) (by norm_num) (sr 2 829601 622201 (by norm_num) (by norm_num) (sr 2 622201 466651 (by norm_num) (by norm_num) (sr 1 466651 699977 (by norm_num) (by norm_num) (sr 2 699977 524983 (by norm_num) (by norm_num) (sr 1 524983 787475 (by norm_num) (by norm_num) (sr 1 787475 1181213 (by norm_num) (by norm_num) (sr 3 1181213 442955 (by norm_num) (by norm_num) (sr 1 442955 664433 (by norm_num) (by norm_num) (sr 2 664433 498325 (by norm_num) (by norm_num) (sr 6 498325 23359 (by norm_num) (by norm_num) (B 23359 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R109251 : Reach 109251 := (sr 1 109251 163877 (by norm_num) (by norm_num) (sr 4 163877 30727 (by norm_num) (by norm_num) (B 30727 (by norm_num) (by norm_num) (by norm_num))))
theorem R109255 : Reach 109255 := (sr 1 109255 163883 (by norm_num) (by norm_num) (sr 1 163883 245825 (by norm_num) (by norm_num) (sr 2 245825 184369 (by norm_num) (by norm_num) (sr 2 184369 138277 (by norm_num) (by norm_num) (sr 4 138277 25927 (by norm_num) (by norm_num) (B 25927 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R109259 : Reach 109259 := (sr 1 109259 163889 (by norm_num) (by norm_num) (sr 2 163889 122917 (by norm_num) (by norm_num) (sr 4 122917 23047 (by norm_num) (by norm_num) (B 23047 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109263 : Reach 109263 := (sr 1 109263 163895 (by norm_num) (by norm_num) (sr 1 163895 245843 (by norm_num) (by norm_num) (sr 1 245843 368765 (by norm_num) (by norm_num) (sr 3 368765 138287 (by norm_num) (by norm_num) (sr 1 138287 207431 (by norm_num) (by norm_num) (sr 1 207431 311147 (by norm_num) (by norm_num) (sr 1 311147 466721 (by norm_num) (by norm_num) (sr 2 466721 350041 (by norm_num) (by norm_num) (sr 2 350041 262531 (by norm_num) (by norm_num) (sr 1 262531 393797 (by norm_num) (by norm_num) (sr 4 393797 73837 (by norm_num) (by norm_num) (B 73837 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R109267 : Reach 109267 := (sr 1 109267 163901 (by norm_num) (by norm_num) (sr 3 163901 61463 (by norm_num) (by norm_num) (B 61463 (by norm_num) (by norm_num) (by norm_num))))
theorem R109271 : Reach 109271 := (sr 1 109271 163907 (by norm_num) (by norm_num) (sr 1 163907 245861 (by norm_num) (by norm_num) (sr 4 245861 46099 (by norm_num) (by norm_num) (B 46099 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109275 : Reach 109275 := (sr 1 109275 163913 (by norm_num) (by norm_num) (sr 2 163913 122935 (by norm_num) (by norm_num) (sr 1 122935 184403 (by norm_num) (by norm_num) (sr 1 184403 276605 (by norm_num) (by norm_num) (sr 3 276605 103727 (by norm_num) (by norm_num) R103727)))))
theorem R109279 : Reach 109279 := (sr 1 109279 163919 (by norm_num) (by norm_num) (sr 1 163919 245879 (by norm_num) (by norm_num) (sr 1 245879 368819 (by norm_num) (by norm_num) (sr 1 368819 553229 (by norm_num) (by norm_num) (sr 3 553229 207461 (by norm_num) (by norm_num) (sr 4 207461 38899 (by norm_num) (by norm_num) (B 38899 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R109283 : Reach 109283 := (sr 1 109283 163925 (by norm_num) (by norm_num) (sr 8 163925 1921 (by norm_num) (by norm_num) (B 1921 (by norm_num) (by norm_num) (by norm_num))))
theorem R109287 : Reach 109287 := (sr 1 109287 163931 (by norm_num) (by norm_num) (sr 1 163931 245897 (by norm_num) (by norm_num) (sr 2 245897 184423 (by norm_num) (by norm_num) (sr 1 184423 276635 (by norm_num) (by norm_num) (sr 1 276635 414953 (by norm_num) (by norm_num) (sr 2 414953 311215 (by norm_num) (by norm_num) (sr 1 311215 466823 (by norm_num) (by norm_num) (sr 1 466823 700235 (by norm_num) (by norm_num) (sr 1 700235 1050353 (by norm_num) (by norm_num) (sr 2 1050353 787765 (by norm_num) (by norm_num) (sr 5 787765 73853 (by norm_num) (by norm_num) (B 73853 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R109291 : Reach 109291 := (sr 1 109291 163937 (by norm_num) (by norm_num) (sr 2 163937 122953 (by norm_num) (by norm_num) (sr 2 122953 92215 (by norm_num) (by norm_num) (B 92215 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109295 : Reach 109295 := (sr 1 109295 163943 (by norm_num) (by norm_num) (sr 1 163943 245915 (by norm_num) (by norm_num) (sr 1 245915 368873 (by norm_num) (by norm_num) (sr 2 368873 276655 (by norm_num) (by norm_num) (sr 1 276655 414983 (by norm_num) (by norm_num) (sr 1 414983 622475 (by norm_num) (by norm_num) (sr 1 622475 933713 (by norm_num) (by norm_num) (sr 2 933713 700285 (by norm_num) (by norm_num) (sr 3 700285 262607 (by norm_num) (by norm_num) (sr 1 262607 393911 (by norm_num) (by norm_num) (sr 1 393911 590867 (by norm_num) (by norm_num) (sr 1 590867 886301 (by norm_num) (by norm_num) (sr 3 886301 332363 (by norm_num) (by norm_num) (sr 1 332363 498545 (by norm_num) (by norm_num) (sr 2 498545 373909 (by norm_num) (by norm_num) (sr 6 373909 17527 (by norm_num) (by norm_num) (B 17527 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))
theorem R109299 : Reach 109299 := (sr 1 109299 163949 (by norm_num) (by norm_num) (sr 3 163949 61481 (by norm_num) (by norm_num) (B 61481 (by norm_num) (by norm_num) (by norm_num))))
theorem R109303 : Reach 109303 := (sr 1 109303 163955 (by norm_num) (by norm_num) (sr 1 163955 245933 (by norm_num) (by norm_num) (sr 3 245933 92225 (by norm_num) (by norm_num) (B 92225 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109307 : Reach 109307 := (sr 1 109307 163961 (by norm_num) (by norm_num) (sr 2 163961 122971 (by norm_num) (by norm_num) (sr 1 122971 184457 (by norm_num) (by norm_num) (sr 2 184457 138343 (by norm_num) (by norm_num) (sr 1 138343 207515 (by norm_num) (by norm_num) (sr 1 207515 311273 (by norm_num) (by norm_num) (sr 2 311273 233455 (by norm_num) (by norm_num) (sr 1 233455 350183 (by norm_num) (by norm_num) (sr 1 350183 525275 (by norm_num) (by norm_num) (sr 1 525275 787913 (by norm_num) (by norm_num) (sr 2 787913 590935 (by norm_num) (by norm_num) (sr 1 590935 886403 (by norm_num) (by norm_num) (sr 1 886403 1329605 (by norm_num) (by norm_num) (sr 4 1329605 249301 (by norm_num) (by norm_num) (sr 7 249301 5843 (by norm_num) (by norm_num) (B 5843 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))
theorem R109311 : Reach 109311 := (sr 1 109311 163967 (by norm_num) (by norm_num) (sr 1 163967 245951 (by norm_num) (by norm_num) (sr 1 245951 368927 (by norm_num) (by norm_num) (sr 1 368927 553391 (by norm_num) (by norm_num) (sr 1 553391 830087 (by norm_num) (by norm_num) (sr 1 830087 1245131 (by norm_num) (by norm_num) (sr 1 1245131 1867697 (by norm_num) (by norm_num) (sr 2 1867697 1400773 (by norm_num) (by norm_num) (sr 4 1400773 262645 (by norm_num) (by norm_num) (sr 5 262645 24623 (by norm_num) (by norm_num) (B 24623 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R109315 : Reach 109315 := (sr 1 109315 163973 (by norm_num) (by norm_num) (sr 4 163973 30745 (by norm_num) (by norm_num) (B 30745 (by norm_num) (by norm_num) (by norm_num))))
theorem R109319 : Reach 109319 := (sr 1 109319 163979 (by norm_num) (by norm_num) (sr 1 163979 245969 (by norm_num) (by norm_num) (sr 2 245969 184477 (by norm_num) (by norm_num) (sr 3 184477 69179 (by norm_num) (by norm_num) (B 69179 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109323 : Reach 109323 := (sr 1 109323 163985 (by norm_num) (by norm_num) (sr 2 163985 122989 (by norm_num) (by norm_num) (sr 3 122989 46121 (by norm_num) (by norm_num) (B 46121 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109327 : Reach 109327 := (sr 1 109327 163991 (by norm_num) (by norm_num) (sr 1 163991 245987 (by norm_num) (by norm_num) (sr 1 245987 368981 (by norm_num) (by norm_num) (sr 10 368981 1081 (by norm_num) (by norm_num) (B 1081 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109331 : Reach 109331 := (sr 1 109331 163997 (by norm_num) (by norm_num) (sr 3 163997 61499 (by norm_num) (by norm_num) (B 61499 (by norm_num) (by norm_num) (by norm_num))))
theorem R109335 : Reach 109335 := (sr 1 109335 164003 (by norm_num) (by norm_num) (sr 1 164003 246005 (by norm_num) (by norm_num) (sr 5 246005 23063 (by norm_num) (by norm_num) (B 23063 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109339 : Reach 109339 := (sr 1 109339 164009 (by norm_num) (by norm_num) (sr 2 164009 123007 (by norm_num) (by norm_num) (sr 1 123007 184511 (by norm_num) (by norm_num) (sr 1 184511 276767 (by norm_num) (by norm_num) (sr 1 276767 415151 (by norm_num) (by norm_num) (sr 1 415151 622727 (by norm_num) (by norm_num) (sr 1 622727 934091 (by norm_num) (by norm_num) (sr 1 934091 1401137 (by norm_num) (by norm_num) (sr 2 1401137 1050853 (by norm_num) (by norm_num) (sr 4 1050853 197035 (by norm_num) (by norm_num) (sr 1 197035 295553 (by norm_num) (by norm_num) (sr 2 295553 221665 (by norm_num) (by norm_num) (sr 2 221665 166249 (by norm_num) (by norm_num) (sr 2 166249 124687 (by norm_num) (by norm_num) (sr 1 124687 187031 (by norm_num) (by norm_num) (sr 1 187031 280547 (by norm_num) (by norm_num) (sr 1 280547 420821 (by norm_num) (by norm_num) (sr 7 420821 9863 (by norm_num) (by norm_num) (B 9863 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))
theorem R109343 : Reach 109343 := (sr 1 109343 164015 (by norm_num) (by norm_num) (sr 1 164015 246023 (by norm_num) (by norm_num) (sr 1 246023 369035 (by norm_num) (by norm_num) (sr 1 369035 553553 (by norm_num) (by norm_num) (sr 2 553553 415165 (by norm_num) (by norm_num) (sr 3 415165 155687 (by norm_num) (by norm_num) (sr 1 155687 233531 (by norm_num) (by norm_num) (sr 1 233531 350297 (by norm_num) (by norm_num) (sr 2 350297 262723 (by norm_num) (by norm_num) (sr 1 262723 394085 (by norm_num) (by norm_num) (sr 4 394085 73891 (by norm_num) (by norm_num) (B 73891 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R109347 : Reach 109347 := (sr 1 109347 164021 (by norm_num) (by norm_num) (sr 5 164021 15377 (by norm_num) (by norm_num) (B 15377 (by norm_num) (by norm_num) (by norm_num))))
theorem R109351 : Reach 109351 := (sr 1 109351 164027 (by norm_num) (by norm_num) (sr 1 164027 246041 (by norm_num) (by norm_num) (sr 2 246041 184531 (by norm_num) (by norm_num) (sr 1 184531 276797 (by norm_num) (by norm_num) (sr 3 276797 103799 (by norm_num) (by norm_num) R103799)))))
theorem R109355 : Reach 109355 := (sr 1 109355 164033 (by norm_num) (by norm_num) (sr 2 164033 123025 (by norm_num) (by norm_num) (sr 2 123025 92269 (by norm_num) (by norm_num) (B 92269 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109359 : Reach 109359 := (sr 1 109359 164039 (by norm_num) (by norm_num) (sr 1 164039 246059 (by norm_num) (by norm_num) (sr 1 246059 369089 (by norm_num) (by norm_num) (sr 2 369089 276817 (by norm_num) (by norm_num) (sr 2 276817 207613 (by norm_num) (by norm_num) (sr 3 207613 77855 (by norm_num) (by norm_num) (B 77855 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R109363 : Reach 109363 := (sr 1 109363 164045 (by norm_num) (by norm_num) (sr 3 164045 61517 (by norm_num) (by norm_num) (B 61517 (by norm_num) (by norm_num) (by norm_num))))
theorem R109367 : Reach 109367 := (sr 1 109367 164051 (by norm_num) (by norm_num) (sr 1 164051 246077 (by norm_num) (by norm_num) (sr 3 246077 92279 (by norm_num) (by norm_num) (B 92279 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109371 : Reach 109371 := (sr 1 109371 164057 (by norm_num) (by norm_num) (sr 2 164057 123043 (by norm_num) (by norm_num) (sr 1 123043 184565 (by norm_num) (by norm_num) (sr 5 184565 17303 (by norm_num) (by norm_num) (B 17303 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109375 : Reach 109375 := (sr 1 109375 164063 (by norm_num) (by norm_num) (sr 1 164063 246095 (by norm_num) (by norm_num) (sr 1 246095 369143 (by norm_num) (by norm_num) (sr 1 369143 553715 (by norm_num) (by norm_num) (sr 1 553715 830573 (by norm_num) (by norm_num) (sr 3 830573 311465 (by norm_num) (by norm_num) (sr 2 311465 233599 (by norm_num) (by norm_num) (sr 1 233599 350399 (by norm_num) (by norm_num) (sr 1 350399 525599 (by norm_num) (by norm_num) (sr 1 525599 788399 (by norm_num) (by norm_num) (sr 1 788399 1182599 (by norm_num) (by norm_num) (sr 1 1182599 1773899 (by norm_num) (by norm_num) (sr 1 1773899 2660849 (by norm_num) (by norm_num) (sr 2 2660849 1995637 (by norm_num) (by norm_num) (sr 5 1995637 187091 (by norm_num) (by norm_num) (sr 1 187091 280637 (by norm_num) (by norm_num) (sr 3 280637 105239 (by norm_num) (by norm_num) R105239)))))))))))))))))
theorem R109379 : Reach 109379 := (sr 1 109379 164069 (by norm_num) (by norm_num) (sr 4 164069 30763 (by norm_num) (by norm_num) (B 30763 (by norm_num) (by norm_num) (by norm_num))))
theorem R109383 : Reach 109383 := (sr 1 109383 164075 (by norm_num) (by norm_num) (sr 1 164075 246113 (by norm_num) (by norm_num) (sr 2 246113 184585 (by norm_num) (by norm_num) (sr 2 184585 138439 (by norm_num) (by norm_num) (sr 1 138439 207659 (by norm_num) (by norm_num) (sr 1 207659 311489 (by norm_num) (by norm_num) (sr 2 311489 233617 (by norm_num) (by norm_num) (sr 2 233617 175213 (by norm_num) (by norm_num) (sr 3 175213 65705 (by norm_num) (by norm_num) (B 65705 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R109387 : Reach 109387 := (sr 1 109387 164081 (by norm_num) (by norm_num) (sr 2 164081 123061 (by norm_num) (by norm_num) (sr 5 123061 11537 (by norm_num) (by norm_num) (B 11537 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109391 : Reach 109391 := (sr 1 109391 164087 (by norm_num) (by norm_num) (sr 1 164087 246131 (by norm_num) (by norm_num) (sr 1 246131 369197 (by norm_num) (by norm_num) (sr 3 369197 138449 (by norm_num) (by norm_num) (sr 2 138449 103837 (by norm_num) (by norm_num) (sr 3 103837 38939 (by norm_num) (by norm_num) (B 38939 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R109395 : Reach 109395 := (sr 1 109395 164093 (by norm_num) (by norm_num) (sr 3 164093 61535 (by norm_num) (by norm_num) (B 61535 (by norm_num) (by norm_num) (by norm_num))))
theorem R109399 : Reach 109399 := (sr 1 109399 164099 (by norm_num) (by norm_num) (sr 1 164099 246149 (by norm_num) (by norm_num) (sr 4 246149 46153 (by norm_num) (by norm_num) (B 46153 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109403 : Reach 109403 := (sr 1 109403 164105 (by norm_num) (by norm_num) (sr 2 164105 123079 (by norm_num) (by norm_num) (sr 1 123079 184619 (by norm_num) (by norm_num) (sr 1 184619 276929 (by norm_num) (by norm_num) (sr 2 276929 207697 (by norm_num) (by norm_num) (sr 2 207697 155773 (by norm_num) (by norm_num) (sr 3 155773 58415 (by norm_num) (by norm_num) (B 58415 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R109407 : Reach 109407 := (sr 1 109407 164111 (by norm_num) (by norm_num) (sr 1 164111 246167 (by norm_num) (by norm_num) (sr 1 246167 369251 (by norm_num) (by norm_num) (sr 1 369251 553877 (by norm_num) (by norm_num) (sr 6 553877 25963 (by norm_num) (by norm_num) (B 25963 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R109411 : Reach 109411 := (sr 1 109411 164117 (by norm_num) (by norm_num) (sr 6 164117 7693 (by norm_num) (by norm_num) (B 7693 (by norm_num) (by norm_num) (by norm_num))))
theorem R109415 : Reach 109415 := (sr 1 109415 164123 (by norm_num) (by norm_num) (sr 1 164123 246185 (by norm_num) (by norm_num) (sr 2 246185 184639 (by norm_num) (by norm_num) (sr 1 184639 276959 (by norm_num) (by norm_num) (sr 1 276959 415439 (by norm_num) (by norm_num) (sr 1 415439 623159 (by norm_num) (by norm_num) (sr 1 623159 934739 (by norm_num) (by norm_num) (sr 1 934739 1402109 (by norm_num) (by norm_num) (sr 3 1402109 525791 (by norm_num) (by norm_num) (sr 1 525791 788687 (by norm_num) (by norm_num) (sr 1 788687 1183031 (by norm_num) (by norm_num) (sr 1 1183031 1774547 (by norm_num) (by norm_num) (sr 1 1774547 2661821 (by norm_num) (by norm_num) (sr 3 2661821 998183 (by norm_num) (by norm_num) (sr 1 998183 1497275 (by norm_num) (by norm_num) (sr 1 1497275 2245913 (by norm_num) (by norm_num) (sr 2 2245913 1684435 (by norm_num) (by norm_num) (sr 1 1684435 2526653 (by norm_num) (by norm_num) (sr 3 2526653 947495 (by norm_num) (by norm_num) (sr 1 947495 1421243 (by norm_num) (by norm_num) (sr 1 1421243 2131865 (by norm_num) (by norm_num) (sr 2 2131865 1598899 (by norm_num) (by norm_num) (sr 1 1598899 2398349 (by norm_num) (by norm_num) (sr 3 2398349 899381 (by norm_num) (by norm_num) (sr 5 899381 84317 (by norm_num) (by norm_num) (B 84317 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))
theorem R109419 : Reach 109419 := (sr 1 109419 164129 (by norm_num) (by norm_num) (sr 2 164129 123097 (by norm_num) (by norm_num) (sr 2 123097 92323 (by norm_num) (by norm_num) (B 92323 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109423 : Reach 109423 := (sr 1 109423 164135 (by norm_num) (by norm_num) (sr 1 164135 246203 (by norm_num) (by norm_num) (sr 1 246203 369305 (by norm_num) (by norm_num) (sr 2 369305 276979 (by norm_num) (by norm_num) (sr 1 276979 415469 (by norm_num) (by norm_num) (sr 3 415469 155801 (by norm_num) (by norm_num) (sr 2 155801 116851 (by norm_num) (by norm_num) (sr 1 116851 175277 (by norm_num) (by norm_num) (sr 3 175277 65729 (by norm_num) (by norm_num) (B 65729 (by norm_num) (by norm_num) (by norm_num)))))))))))
theorem R109427 : Reach 109427 := (sr 1 109427 164141 (by norm_num) (by norm_num) (sr 3 164141 61553 (by norm_num) (by norm_num) (B 61553 (by norm_num) (by norm_num) (by norm_num))))
theorem R109431 : Reach 109431 := (sr 1 109431 164147 (by norm_num) (by norm_num) (sr 1 164147 246221 (by norm_num) (by norm_num) (sr 3 246221 92333 (by norm_num) (by norm_num) (B 92333 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109435 : Reach 109435 := (sr 1 109435 164153 (by norm_num) (by norm_num) (sr 2 164153 123115 (by norm_num) (by norm_num) (sr 1 123115 184673 (by norm_num) (by norm_num) (sr 2 184673 138505 (by norm_num) (by norm_num) (sr 2 138505 103879 (by norm_num) (by norm_num) R103879)))))
theorem R109439 : Reach 109439 := (sr 1 109439 164159 (by norm_num) (by norm_num) (sr 1 164159 246239 (by norm_num) (by norm_num) (sr 1 246239 369359 (by norm_num) (by norm_num) (sr 1 369359 554039 (by norm_num) (by norm_num) (sr 1 554039 831059 (by norm_num) (by norm_num) (sr 1 831059 1246589 (by norm_num) (by norm_num) (sr 3 1246589 467471 (by norm_num) (by norm_num) (sr 1 467471 701207 (by norm_num) (by norm_num) (sr 1 701207 1051811 (by norm_num) (by norm_num) (sr 1 1051811 1577717 (by norm_num) (by norm_num) (sr 5 1577717 147911 (by norm_num) (by norm_num) (sr 1 147911 221867 (by norm_num) (by norm_num) (sr 1 221867 332801 (by norm_num) (by norm_num) (sr 2 332801 249601 (by norm_num) (by norm_num) (sr 2 249601 187201 (by norm_num) (by norm_num) (sr 2 187201 140401 (by norm_num) (by norm_num) (sr 2 140401 105301 (by norm_num) (by norm_num) (sr 9 105301 617 (by norm_num) (by norm_num) (B 617 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))
theorem R109443 : Reach 109443 := (sr 1 109443 164165 (by norm_num) (by norm_num) (sr 4 164165 30781 (by norm_num) (by norm_num) (B 30781 (by norm_num) (by norm_num) (by norm_num))))
theorem R109447 : Reach 109447 := (sr 1 109447 164171 (by norm_num) (by norm_num) (sr 1 164171 246257 (by norm_num) (by norm_num) (sr 2 246257 184693 (by norm_num) (by norm_num) (sr 5 184693 17315 (by norm_num) (by norm_num) (B 17315 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109451 : Reach 109451 := (sr 1 109451 164177 (by norm_num) (by norm_num) (sr 2 164177 123133 (by norm_num) (by norm_num) (sr 3 123133 46175 (by norm_num) (by norm_num) (B 46175 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109455 : Reach 109455 := (sr 1 109455 164183 (by norm_num) (by norm_num) (sr 1 164183 246275 (by norm_num) (by norm_num) (sr 1 246275 369413 (by norm_num) (by norm_num) (sr 4 369413 69265 (by norm_num) (by norm_num) (B 69265 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109459 : Reach 109459 := (sr 1 109459 164189 (by norm_num) (by norm_num) (sr 3 164189 61571 (by norm_num) (by norm_num) (B 61571 (by norm_num) (by norm_num) (by norm_num))))
theorem R109463 : Reach 109463 := (sr 1 109463 164195 (by norm_num) (by norm_num) (sr 1 164195 246293 (by norm_num) (by norm_num) (sr 6 246293 11545 (by norm_num) (by norm_num) (B 11545 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109467 : Reach 109467 := (sr 1 109467 164201 (by norm_num) (by norm_num) (sr 2 164201 123151 (by norm_num) (by norm_num) (sr 1 123151 184727 (by norm_num) (by norm_num) (sr 1 184727 277091 (by norm_num) (by norm_num) (sr 1 277091 415637 (by norm_num) (by norm_num) (sr 6 415637 19483 (by norm_num) (by norm_num) (B 19483 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R109471 : Reach 109471 := (sr 1 109471 164207 (by norm_num) (by norm_num) (sr 1 164207 246311 (by norm_num) (by norm_num) (sr 1 246311 369467 (by norm_num) (by norm_num) (sr 1 369467 554201 (by norm_num) (by norm_num) (sr 2 554201 415651 (by norm_num) (by norm_num) (sr 1 415651 623477 (by norm_num) (by norm_num) (sr 5 623477 58451 (by norm_num) (by norm_num) (B 58451 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R109475 : Reach 109475 := (sr 1 109475 164213 (by norm_num) (by norm_num) (sr 5 164213 15395 (by norm_num) (by norm_num) (B 15395 (by norm_num) (by norm_num) (by norm_num))))
theorem R109479 : Reach 109479 := (sr 1 109479 164219 (by norm_num) (by norm_num) (sr 1 164219 246329 (by norm_num) (by norm_num) (sr 2 246329 184747 (by norm_num) (by norm_num) (sr 1 184747 277121 (by norm_num) (by norm_num) (sr 2 277121 207841 (by norm_num) (by norm_num) (sr 2 207841 155881 (by norm_num) (by norm_num) (sr 2 155881 116911 (by norm_num) (by norm_num) (sr 1 116911 175367 (by norm_num) (by norm_num) (sr 1 175367 263051 (by norm_num) (by norm_num) (sr 1 263051 394577 (by norm_num) (by norm_num) (sr 2 394577 295933 (by norm_num) (by norm_num) (sr 3 295933 110975 (by norm_num) (by norm_num) (sr 1 110975 166463 (by norm_num) (by norm_num) (sr 1 166463 249695 (by norm_num) (by norm_num) (sr 1 249695 374543 (by norm_num) (by norm_num) (sr 1 374543 561815 (by norm_num) (by norm_num) (sr 1 561815 842723 (by norm_num) (by norm_num) (sr 1 842723 1264085 (by norm_num) (by norm_num) (sr 7 1264085 29627 (by norm_num) (by norm_num) (B 29627 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))
theorem R109483 : Reach 109483 := (sr 1 109483 164225 (by norm_num) (by norm_num) (sr 2 164225 123169 (by norm_num) (by norm_num) (sr 2 123169 92377 (by norm_num) (by norm_num) (B 92377 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109487 : Reach 109487 := (sr 1 109487 164231 (by norm_num) (by norm_num) (sr 1 164231 246347 (by norm_num) (by norm_num) (sr 1 246347 369521 (by norm_num) (by norm_num) (sr 2 369521 277141 (by norm_num) (by norm_num) (sr 6 277141 12991 (by norm_num) (by norm_num) (B 12991 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R109491 : Reach 109491 := (sr 1 109491 164237 (by norm_num) (by norm_num) (sr 3 164237 61589 (by norm_num) (by norm_num) (B 61589 (by norm_num) (by norm_num) (by norm_num))))
theorem R109495 : Reach 109495 := (sr 1 109495 164243 (by norm_num) (by norm_num) (sr 1 164243 246365 (by norm_num) (by norm_num) (sr 3 246365 92387 (by norm_num) (by norm_num) (B 92387 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109499 : Reach 109499 := (sr 1 109499 164249 (by norm_num) (by norm_num) (sr 2 164249 123187 (by norm_num) (by norm_num) (sr 1 123187 184781 (by norm_num) (by norm_num) (sr 3 184781 69293 (by norm_num) (by norm_num) (B 69293 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109503 : Reach 109503 := (sr 1 109503 164255 (by norm_num) (by norm_num) (sr 1 164255 246383 (by norm_num) (by norm_num) (sr 1 246383 369575 (by norm_num) (by norm_num) (sr 1 369575 554363 (by norm_num) (by norm_num) (sr 1 554363 831545 (by norm_num) (by norm_num) (sr 2 831545 623659 (by norm_num) (by norm_num) (sr 1 623659 935489 (by norm_num) (by norm_num) (sr 2 935489 701617 (by norm_num) (by norm_num) (sr 2 701617 526213 (by norm_num) (by norm_num) (sr 4 526213 98665 (by norm_num) (by norm_num) (B 98665 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R109507 : Reach 109507 := (sr 1 109507 164261 (by norm_num) (by norm_num) (sr 4 164261 30799 (by norm_num) (by norm_num) (B 30799 (by norm_num) (by norm_num) (by norm_num))))
theorem R109511 : Reach 109511 := (sr 1 109511 164267 (by norm_num) (by norm_num) (sr 1 164267 246401 (by norm_num) (by norm_num) (sr 2 246401 184801 (by norm_num) (by norm_num) (sr 2 184801 138601 (by norm_num) (by norm_num) (sr 2 138601 103951 (by norm_num) (by norm_num) R103951)))))
theorem R109515 : Reach 109515 := (sr 1 109515 164273 (by norm_num) (by norm_num) (sr 2 164273 123205 (by norm_num) (by norm_num) (sr 4 123205 23101 (by norm_num) (by norm_num) (B 23101 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109519 : Reach 109519 := (sr 1 109519 164279 (by norm_num) (by norm_num) (sr 1 164279 246419 (by norm_num) (by norm_num) (sr 1 246419 369629 (by norm_num) (by norm_num) (sr 3 369629 138611 (by norm_num) (by norm_num) (sr 1 138611 207917 (by norm_num) (by norm_num) (sr 3 207917 77969 (by norm_num) (by norm_num) (B 77969 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R109523 : Reach 109523 := (sr 1 109523 164285 (by norm_num) (by norm_num) (sr 3 164285 61607 (by norm_num) (by norm_num) (B 61607 (by norm_num) (by norm_num) (by norm_num))))
theorem R109527 : Reach 109527 := (sr 1 109527 164291 (by norm_num) (by norm_num) (sr 1 164291 246437 (by norm_num) (by norm_num) (sr 4 246437 46207 (by norm_num) (by norm_num) (B 46207 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109531 : Reach 109531 := (sr 1 109531 164297 (by norm_num) (by norm_num) (sr 2 164297 123223 (by norm_num) (by norm_num) (sr 1 123223 184835 (by norm_num) (by norm_num) (sr 1 184835 277253 (by norm_num) (by norm_num) (sr 4 277253 51985 (by norm_num) (by norm_num) (B 51985 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R109535 : Reach 109535 := (sr 1 109535 164303 (by norm_num) (by norm_num) (sr 1 164303 246455 (by norm_num) (by norm_num) (sr 1 246455 369683 (by norm_num) (by norm_num) (sr 1 369683 554525 (by norm_num) (by norm_num) (sr 3 554525 207947 (by norm_num) (by norm_num) (sr 1 207947 311921 (by norm_num) (by norm_num) (sr 2 311921 233941 (by norm_num) (by norm_num) (sr 7 233941 5483 (by norm_num) (by norm_num) (B 5483 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R109539 : Reach 109539 := (sr 1 109539 164309 (by norm_num) (by norm_num) (sr 7 164309 3851 (by norm_num) (by norm_num) (B 3851 (by norm_num) (by norm_num) (by norm_num))))
theorem R109543 : Reach 109543 := (sr 1 109543 164315 (by norm_num) (by norm_num) (sr 1 164315 246473 (by norm_num) (by norm_num) (sr 2 246473 184855 (by norm_num) (by norm_num) (sr 1 184855 277283 (by norm_num) (by norm_num) (sr 1 277283 415925 (by norm_num) (by norm_num) (sr 5 415925 38993 (by norm_num) (by norm_num) (B 38993 (by norm_num) (by norm_num) (by norm_num))))))))
theorem R109547 : Reach 109547 := (sr 1 109547 164321 (by norm_num) (by norm_num) (sr 2 164321 123241 (by norm_num) (by norm_num) (sr 2 123241 92431 (by norm_num) (by norm_num) (B 92431 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109551 : Reach 109551 := (sr 1 109551 164327 (by norm_num) (by norm_num) (sr 1 164327 246491 (by norm_num) (by norm_num) (sr 1 246491 369737 (by norm_num) (by norm_num) (sr 2 369737 277303 (by norm_num) (by norm_num) (sr 1 277303 415955 (by norm_num) (by norm_num) (sr 1 415955 623933 (by norm_num) (by norm_num) (sr 3 623933 233975 (by norm_num) (by norm_num) (sr 1 233975 350963 (by norm_num) (by norm_num) (sr 1 350963 526445 (by norm_num) (by norm_num) (sr 3 526445 197417 (by norm_num) (by norm_num) (sr 2 197417 148063 (by norm_num) (by norm_num) (sr 1 148063 222095 (by norm_num) (by norm_num) (sr 1 222095 333143 (by norm_num) (by norm_num) (sr 1 333143 499715 (by norm_num) (by norm_num) (sr 1 499715 749573 (by norm_num) (by norm_num) (sr 4 749573 140545 (by norm_num) (by norm_num) (sr 2 140545 105409 (by norm_num) (by norm_num) (sr 2 105409 79057 (by norm_num) (by norm_num) (B 79057 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))
theorem R109555 : Reach 109555 := (sr 1 109555 164333 (by norm_num) (by norm_num) (sr 3 164333 61625 (by norm_num) (by norm_num) (B 61625 (by norm_num) (by norm_num) (by norm_num))))
theorem R109559 : Reach 109559 := (sr 1 109559 164339 (by norm_num) (by norm_num) (sr 1 164339 246509 (by norm_num) (by norm_num) (sr 3 246509 92441 (by norm_num) (by norm_num) (B 92441 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109563 : Reach 109563 := (sr 1 109563 164345 (by norm_num) (by norm_num) (sr 2 164345 123259 (by norm_num) (by norm_num) (sr 1 123259 184889 (by norm_num) (by norm_num) (sr 2 184889 138667 (by norm_num) (by norm_num) (sr 1 138667 208001 (by norm_num) (by norm_num) (sr 2 208001 156001 (by norm_num) (by norm_num) (sr 2 156001 117001 (by norm_num) (by norm_num) (sr 2 117001 87751 (by norm_num) (by norm_num) (B 87751 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R109567 : Reach 109567 := (sr 1 109567 164351 (by norm_num) (by norm_num) (sr 1 164351 246527 (by norm_num) (by norm_num) (sr 1 246527 369791 (by norm_num) (by norm_num) (sr 1 369791 554687 (by norm_num) (by norm_num) (sr 1 554687 832031 (by norm_num) (by norm_num) (sr 1 832031 1248047 (by norm_num) (by norm_num) (sr 1 1248047 1872071 (by norm_num) (by norm_num) (sr 1 1872071 2808107 (by norm_num) (by norm_num) (sr 1 2808107 4212161 (by norm_num) (by norm_num) (sr 2 4212161 3159121 (by norm_num) (by norm_num) (sr 2 3159121 2369341 (by norm_num) (by norm_num) (sr 3 2369341 888503 (by norm_num) (by norm_num) (sr 1 888503 1332755 (by norm_num) (by norm_num) (sr 1 1332755 1999133 (by norm_num) (by norm_num) (sr 3 1999133 749675 (by norm_num) (by norm_num) (sr 1 749675 1124513 (by norm_num) (by norm_num) (sr 2 1124513 843385 (by norm_num) (by norm_num) (sr 2 843385 632539 (by norm_num) (by norm_num) (sr 1 632539 948809 (by norm_num) (by norm_num) (sr 2 948809 711607 (by norm_num) (by norm_num) (sr 1 711607 1067411 (by norm_num) (by norm_num) (sr 1 1067411 1601117 (by norm_num) (by norm_num) (sr 3 1601117 600419 (by norm_num) (by norm_num) (sr 1 600419 900629 (by norm_num) (by norm_num) (sr 6 900629 42217 (by norm_num) (by norm_num) (B 42217 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))))))
theorem R109571 : Reach 109571 := (sr 1 109571 164357 (by norm_num) (by norm_num) (sr 4 164357 30817 (by norm_num) (by norm_num) (B 30817 (by norm_num) (by norm_num) (by norm_num))))
theorem R109575 : Reach 109575 := (sr 1 109575 164363 (by norm_num) (by norm_num) (sr 1 164363 246545 (by norm_num) (by norm_num) (sr 2 246545 184909 (by norm_num) (by norm_num) (sr 3 184909 69341 (by norm_num) (by norm_num) (B 69341 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109579 : Reach 109579 := (sr 1 109579 164369 (by norm_num) (by norm_num) (sr 2 164369 123277 (by norm_num) (by norm_num) (sr 3 123277 46229 (by norm_num) (by norm_num) (B 46229 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109583 : Reach 109583 := (sr 1 109583 164375 (by norm_num) (by norm_num) (sr 1 164375 246563 (by norm_num) (by norm_num) (sr 1 246563 369845 (by norm_num) (by norm_num) (sr 5 369845 34673 (by norm_num) (by norm_num) (B 34673 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109587 : Reach 109587 := (sr 1 109587 164381 (by norm_num) (by norm_num) (sr 3 164381 61643 (by norm_num) (by norm_num) (B 61643 (by norm_num) (by norm_num) (by norm_num))))
theorem R109591 : Reach 109591 := (sr 1 109591 164387 (by norm_num) (by norm_num) (sr 1 164387 246581 (by norm_num) (by norm_num) (sr 5 246581 23117 (by norm_num) (by norm_num) (B 23117 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109595 : Reach 109595 := (sr 1 109595 164393 (by norm_num) (by norm_num) (sr 2 164393 123295 (by norm_num) (by norm_num) (sr 1 123295 184943 (by norm_num) (by norm_num) (sr 1 184943 277415 (by norm_num) (by norm_num) (sr 1 277415 416123 (by norm_num) (by norm_num) (sr 1 416123 624185 (by norm_num) (by norm_num) (sr 2 624185 468139 (by norm_num) (by norm_num) (sr 1 468139 702209 (by norm_num) (by norm_num) (sr 2 702209 526657 (by norm_num) (by norm_num) (sr 2 526657 394993 (by norm_num) (by norm_num) (sr 2 394993 296245 (by norm_num) (by norm_num) (sr 5 296245 27773 (by norm_num) (by norm_num) (B 27773 (by norm_num) (by norm_num) (by norm_num))))))))))))))
theorem R109599 : Reach 109599 := (sr 1 109599 164399 (by norm_num) (by norm_num) (sr 1 164399 246599 (by norm_num) (by norm_num) (sr 1 246599 369899 (by norm_num) (by norm_num) (sr 1 369899 554849 (by norm_num) (by norm_num) (sr 2 554849 416137 (by norm_num) (by norm_num) (sr 2 416137 312103 (by norm_num) (by norm_num) (sr 1 312103 468155 (by norm_num) (by norm_num) (sr 1 468155 702233 (by norm_num) (by norm_num) (sr 2 702233 526675 (by norm_num) (by norm_num) (sr 1 526675 790013 (by norm_num) (by norm_num) (sr 3 790013 296255 (by norm_num) (by norm_num) (sr 1 296255 444383 (by norm_num) (by norm_num) (sr 1 444383 666575 (by norm_num) (by norm_num) (sr 1 666575 999863 (by norm_num) (by norm_num) (sr 1 999863 1499795 (by norm_num) (by norm_num) (sr 1 1499795 2249693 (by norm_num) (by norm_num) (sr 3 2249693 843635 (by norm_num) (by norm_num) (sr 1 843635 1265453 (by norm_num) (by norm_num) (sr 3 1265453 474545 (by norm_num) (by norm_num) (sr 2 474545 355909 (by norm_num) (by norm_num) (sr 4 355909 66733 (by norm_num) (by norm_num) (B 66733 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))))))
theorem R109603 : Reach 109603 := (sr 1 109603 164405 (by norm_num) (by norm_num) (sr 5 164405 15413 (by norm_num) (by norm_num) (B 15413 (by norm_num) (by norm_num) (by norm_num))))
theorem R109607 : Reach 109607 := (sr 1 109607 164411 (by norm_num) (by norm_num) (sr 1 164411 246617 (by norm_num) (by norm_num) (sr 2 246617 184963 (by norm_num) (by norm_num) (sr 1 184963 277445 (by norm_num) (by norm_num) (sr 4 277445 52021 (by norm_num) (by norm_num) (B 52021 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R109611 : Reach 109611 := (sr 1 109611 164417 (by norm_num) (by norm_num) (sr 2 164417 123313 (by norm_num) (by norm_num) (sr 2 123313 92485 (by norm_num) (by norm_num) (B 92485 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109615 : Reach 109615 := (sr 1 109615 164423 (by norm_num) (by norm_num) (sr 1 164423 246635 (by norm_num) (by norm_num) (sr 1 246635 369953 (by norm_num) (by norm_num) (sr 2 369953 277465 (by norm_num) (by norm_num) (sr 2 277465 208099 (by norm_num) (by norm_num) (sr 1 208099 312149 (by norm_num) (by norm_num) (sr 9 312149 1829 (by norm_num) (by norm_num) (B 1829 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R109619 : Reach 109619 := (sr 1 109619 164429 (by norm_num) (by norm_num) (sr 3 164429 61661 (by norm_num) (by norm_num) (B 61661 (by norm_num) (by norm_num) (by norm_num))))
theorem R109623 : Reach 109623 := (sr 1 109623 164435 (by norm_num) (by norm_num) (sr 1 164435 246653 (by norm_num) (by norm_num) (sr 3 246653 92495 (by norm_num) (by norm_num) (B 92495 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109627 : Reach 109627 := (sr 1 109627 164441 (by norm_num) (by norm_num) (sr 2 164441 123331 (by norm_num) (by norm_num) (sr 1 123331 184997 (by norm_num) (by norm_num) (sr 4 184997 34687 (by norm_num) (by norm_num) (B 34687 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109631 : Reach 109631 := (sr 1 109631 164447 (by norm_num) (by norm_num) (sr 1 164447 246671 (by norm_num) (by norm_num) (sr 1 246671 370007 (by norm_num) (by norm_num) (sr 1 370007 555011 (by norm_num) (by norm_num) (sr 1 555011 832517 (by norm_num) (by norm_num) (sr 4 832517 156097 (by norm_num) (by norm_num) (sr 2 156097 117073 (by norm_num) (by norm_num) (sr 2 117073 87805 (by norm_num) (by norm_num) (B 87805 (by norm_num) (by norm_num) (by norm_num))))))))))
theorem R109635 : Reach 109635 := (sr 1 109635 164453 (by norm_num) (by norm_num) (sr 4 164453 30835 (by norm_num) (by norm_num) (B 30835 (by norm_num) (by norm_num) (by norm_num))))
theorem R109639 : Reach 109639 := (sr 1 109639 164459 (by norm_num) (by norm_num) (sr 1 164459 246689 (by norm_num) (by norm_num) (sr 2 246689 185017 (by norm_num) (by norm_num) (sr 2 185017 138763 (by norm_num) (by norm_num) (sr 1 138763 208145 (by norm_num) (by norm_num) (sr 2 208145 156109 (by norm_num) (by norm_num) (sr 3 156109 58541 (by norm_num) (by norm_num) (B 58541 (by norm_num) (by norm_num) (by norm_num)))))))))
theorem R109643 : Reach 109643 := (sr 1 109643 164465 (by norm_num) (by norm_num) (sr 2 164465 123349 (by norm_num) (by norm_num) (sr 7 123349 2891 (by norm_num) (by norm_num) (B 2891 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109647 : Reach 109647 := (sr 1 109647 164471 (by norm_num) (by norm_num) (sr 1 164471 246707 (by norm_num) (by norm_num) (sr 1 246707 370061 (by norm_num) (by norm_num) (sr 3 370061 138773 (by norm_num) (by norm_num) (sr 6 138773 6505 (by norm_num) (by norm_num) (B 6505 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R109651 : Reach 109651 := (sr 1 109651 164477 (by norm_num) (by norm_num) (sr 3 164477 61679 (by norm_num) (by norm_num) (B 61679 (by norm_num) (by norm_num) (by norm_num))))
theorem R109655 : Reach 109655 := (sr 1 109655 164483 (by norm_num) (by norm_num) (sr 1 164483 246725 (by norm_num) (by norm_num) (sr 4 246725 46261 (by norm_num) (by norm_num) (B 46261 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109659 : Reach 109659 := (sr 1 109659 164489 (by norm_num) (by norm_num) (sr 2 164489 123367 (by norm_num) (by norm_num) (sr 1 123367 185051 (by norm_num) (by norm_num) (sr 1 185051 277577 (by norm_num) (by norm_num) (sr 2 277577 208183 (by norm_num) (by norm_num) (sr 1 208183 312275 (by norm_num) (by norm_num) (sr 1 312275 468413 (by norm_num) (by norm_num) (sr 3 468413 175655 (by norm_num) (by norm_num) (sr 1 175655 263483 (by norm_num) (by norm_num) (sr 1 263483 395225 (by norm_num) (by norm_num) (sr 2 395225 296419 (by norm_num) (by norm_num) (sr 1 296419 444629 (by norm_num) (by norm_num) (sr 7 444629 10421 (by norm_num) (by norm_num) (B 10421 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R109663 : Reach 109663 := (sr 1 109663 164495 (by norm_num) (by norm_num) (sr 1 164495 246743 (by norm_num) (by norm_num) (sr 1 246743 370115 (by norm_num) (by norm_num) (sr 1 370115 555173 (by norm_num) (by norm_num) (sr 4 555173 104095 (by norm_num) (by norm_num) R104095)))))
theorem R109667 : Reach 109667 := (sr 1 109667 164501 (by norm_num) (by norm_num) (sr 6 164501 7711 (by norm_num) (by norm_num) (B 7711 (by norm_num) (by norm_num) (by norm_num))))
theorem R109671 : Reach 109671 := (sr 1 109671 164507 (by norm_num) (by norm_num) (sr 1 164507 246761 (by norm_num) (by norm_num) (sr 2 246761 185071 (by norm_num) (by norm_num) (sr 1 185071 277607 (by norm_num) (by norm_num) (sr 1 277607 416411 (by norm_num) (by norm_num) (sr 1 416411 624617 (by norm_num) (by norm_num) (sr 2 624617 468463 (by norm_num) (by norm_num) (sr 1 468463 702695 (by norm_num) (by norm_num) (sr 1 702695 1054043 (by norm_num) (by norm_num) (sr 1 1054043 1581065 (by norm_num) (by norm_num) (sr 2 1581065 1185799 (by norm_num) (by norm_num) (sr 1 1185799 1778699 (by norm_num) (by norm_num) (sr 1 1778699 2668049 (by norm_num) (by norm_num) (sr 2 2668049 2001037 (by norm_num) (by norm_num) (sr 3 2001037 750389 (by norm_num) (by norm_num) (sr 5 750389 70349 (by norm_num) (by norm_num) (B 70349 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))
theorem R109675 : Reach 109675 := (sr 1 109675 164513 (by norm_num) (by norm_num) (sr 2 164513 123385 (by norm_num) (by norm_num) (sr 2 123385 92539 (by norm_num) (by norm_num) (B 92539 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109679 : Reach 109679 := (sr 1 109679 164519 (by norm_num) (by norm_num) (sr 1 164519 246779 (by norm_num) (by norm_num) (sr 1 246779 370169 (by norm_num) (by norm_num) (sr 2 370169 277627 (by norm_num) (by norm_num) (sr 1 277627 416441 (by norm_num) (by norm_num) (sr 2 416441 312331 (by norm_num) (by norm_num) (sr 1 312331 468497 (by norm_num) (by norm_num) (sr 2 468497 351373 (by norm_num) (by norm_num) (sr 3 351373 131765 (by norm_num) (by norm_num) (sr 5 131765 12353 (by norm_num) (by norm_num) (B 12353 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R109683 : Reach 109683 := (sr 1 109683 164525 (by norm_num) (by norm_num) (sr 3 164525 61697 (by norm_num) (by norm_num) (B 61697 (by norm_num) (by norm_num) (by norm_num))))
theorem R109687 : Reach 109687 := (sr 1 109687 164531 (by norm_num) (by norm_num) (sr 1 164531 246797 (by norm_num) (by norm_num) (sr 3 246797 92549 (by norm_num) (by norm_num) (B 92549 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109691 : Reach 109691 := (sr 1 109691 164537 (by norm_num) (by norm_num) (sr 2 164537 123403 (by norm_num) (by norm_num) (sr 1 123403 185105 (by norm_num) (by norm_num) (sr 2 185105 138829 (by norm_num) (by norm_num) (sr 3 138829 52061 (by norm_num) (by norm_num) (B 52061 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R109695 : Reach 109695 := (sr 1 109695 164543 (by norm_num) (by norm_num) (sr 1 164543 246815 (by norm_num) (by norm_num) (sr 1 246815 370223 (by norm_num) (by norm_num) (sr 1 370223 555335 (by norm_num) (by norm_num) (sr 1 555335 833003 (by norm_num) (by norm_num) (sr 1 833003 1249505 (by norm_num) (by norm_num) (sr 2 1249505 937129 (by norm_num) (by norm_num) (sr 2 937129 702847 (by norm_num) (by norm_num) (sr 1 702847 1054271 (by norm_num) (by norm_num) (sr 1 1054271 1581407 (by norm_num) (by norm_num) (sr 1 1581407 2372111 (by norm_num) (by norm_num) (sr 1 2372111 3558167 (by norm_num) (by norm_num) (sr 1 3558167 5337251 (by norm_num) (by norm_num) (sr 1 5337251 8005877 (by norm_num) (by norm_num) (sr 5 8005877 750551 (by norm_num) (by norm_num) (sr 1 750551 1125827 (by norm_num) (by norm_num) (sr 1 1125827 1688741 (by norm_num) (by norm_num) (sr 4 1688741 316639 (by norm_num) (by norm_num) (sr 1 316639 474959 (by norm_num) (by norm_num) (sr 1 474959 712439 (by norm_num) (by norm_num) (sr 1 712439 1068659 (by norm_num) (by norm_num) (sr 1 1068659 1602989 (by norm_num) (by norm_num) (sr 3 1602989 601121 (by norm_num) (by norm_num) (sr 2 601121 450841 (by norm_num) (by norm_num) (sr 2 450841 338131 (by norm_num) (by norm_num) (sr 1 338131 507197 (by norm_num) (by norm_num) (sr 3 507197 190199 (by norm_num) (by norm_num) (sr 1 190199 285299 (by norm_num) (by norm_num) (sr 1 285299 427949 (by norm_num) (by norm_num) (sr 3 427949 160481 (by norm_num) (by norm_num) (sr 2 160481 120361 (by norm_num) (by norm_num) (sr 2 120361 90271 (by norm_num) (by norm_num) (B 90271 (by norm_num) (by norm_num) (by norm_num))))))))))))))))))))))))))))))))))
theorem R109699 : Reach 109699 := (sr 1 109699 164549 (by norm_num) (by norm_num) (sr 4 164549 30853 (by norm_num) (by norm_num) (B 30853 (by norm_num) (by norm_num) (by norm_num))))
theorem R109703 : Reach 109703 := (sr 1 109703 164555 (by norm_num) (by norm_num) (sr 1 164555 246833 (by norm_num) (by norm_num) (sr 2 246833 185125 (by norm_num) (by norm_num) (sr 4 185125 34711 (by norm_num) (by norm_num) (B 34711 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109707 : Reach 109707 := (sr 1 109707 164561 (by norm_num) (by norm_num) (sr 2 164561 123421 (by norm_num) (by norm_num) (sr 3 123421 46283 (by norm_num) (by norm_num) (B 46283 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109711 : Reach 109711 := (sr 1 109711 164567 (by norm_num) (by norm_num) (sr 1 164567 246851 (by norm_num) (by norm_num) (sr 1 246851 370277 (by norm_num) (by norm_num) (sr 4 370277 69427 (by norm_num) (by norm_num) (B 69427 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109715 : Reach 109715 := (sr 1 109715 164573 (by norm_num) (by norm_num) (sr 3 164573 61715 (by norm_num) (by norm_num) (B 61715 (by norm_num) (by norm_num) (by norm_num))))
theorem R109719 : Reach 109719 := (sr 1 109719 164579 (by norm_num) (by norm_num) (sr 1 164579 246869 (by norm_num) (by norm_num) (sr 8 246869 2893 (by norm_num) (by norm_num) (B 2893 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109723 : Reach 109723 := (sr 1 109723 164585 (by norm_num) (by norm_num) (sr 2 164585 123439 (by norm_num) (by norm_num) (sr 1 123439 185159 (by norm_num) (by norm_num) (sr 1 185159 277739 (by norm_num) (by norm_num) (sr 1 277739 416609 (by norm_num) (by norm_num) (sr 2 416609 312457 (by norm_num) (by norm_num) (sr 2 312457 234343 (by norm_num) (by norm_num) (sr 1 234343 351515 (by norm_num) (by norm_num) (sr 1 351515 527273 (by norm_num) (by norm_num) (sr 2 527273 395455 (by norm_num) (by norm_num) (sr 1 395455 593183 (by norm_num) (by norm_num) (sr 1 593183 889775 (by norm_num) (by norm_num) (sr 1 889775 1334663 (by norm_num) (by norm_num) (sr 1 1334663 2001995 (by norm_num) (by norm_num) (sr 1 2001995 3002993 (by norm_num) (by norm_num) (sr 2 3002993 2252245 (by norm_num) (by norm_num) (sr 7 2252245 52787 (by norm_num) (by norm_num) (B 52787 (by norm_num) (by norm_num) (by norm_num)))))))))))))))))))
theorem R109727 : Reach 109727 := (sr 1 109727 164591 (by norm_num) (by norm_num) (sr 1 164591 246887 (by norm_num) (by norm_num) (sr 1 246887 370331 (by norm_num) (by norm_num) (sr 1 370331 555497 (by norm_num) (by norm_num) (sr 2 555497 416623 (by norm_num) (by norm_num) (sr 1 416623 624935 (by norm_num) (by norm_num) (sr 1 624935 937403 (by norm_num) (by norm_num) (sr 1 937403 1406105 (by norm_num) (by norm_num) (sr 2 1406105 1054579 (by norm_num) (by norm_num) (sr 1 1054579 1581869 (by norm_num) (by norm_num) (sr 3 1581869 593201 (by norm_num) (by norm_num) (sr 2 593201 444901 (by norm_num) (by norm_num) (sr 4 444901 83419 (by norm_num) (by norm_num) (B 83419 (by norm_num) (by norm_num) (by norm_num)))))))))))))))
theorem R109731 : Reach 109731 := (sr 1 109731 164597 (by norm_num) (by norm_num) (sr 5 164597 15431 (by norm_num) (by norm_num) (B 15431 (by norm_num) (by norm_num) (by norm_num))))
theorem R109735 : Reach 109735 := (sr 1 109735 164603 (by norm_num) (by norm_num) (sr 1 164603 246905 (by norm_num) (by norm_num) (sr 2 246905 185179 (by norm_num) (by norm_num) (sr 1 185179 277769 (by norm_num) (by norm_num) (sr 2 277769 208327 (by norm_num) (by norm_num) (sr 1 208327 312491 (by norm_num) (by norm_num) (sr 1 312491 468737 (by norm_num) (by norm_num) (sr 2 468737 351553 (by norm_num) (by norm_num) (sr 2 351553 263665 (by norm_num) (by norm_num) (sr 2 263665 197749 (by norm_num) (by norm_num) (sr 5 197749 18539 (by norm_num) (by norm_num) (B 18539 (by norm_num) (by norm_num) (by norm_num)))))))))))))
theorem R109739 : Reach 109739 := (sr 1 109739 164609 (by norm_num) (by norm_num) (sr 2 164609 123457 (by norm_num) (by norm_num) (sr 2 123457 92593 (by norm_num) (by norm_num) (B 92593 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109743 : Reach 109743 := (sr 1 109743 164615 (by norm_num) (by norm_num) (sr 1 164615 246923 (by norm_num) (by norm_num) (sr 1 246923 370385 (by norm_num) (by norm_num) (sr 2 370385 277789 (by norm_num) (by norm_num) (sr 3 277789 104171 (by norm_num) (by norm_num) R104171)))))
theorem R109747 : Reach 109747 := (sr 1 109747 164621 (by norm_num) (by norm_num) (sr 3 164621 61733 (by norm_num) (by norm_num) (B 61733 (by norm_num) (by norm_num) (by norm_num))))
theorem R109751 : Reach 109751 := (sr 1 109751 164627 (by norm_num) (by norm_num) (sr 1 164627 246941 (by norm_num) (by norm_num) (sr 3 246941 92603 (by norm_num) (by norm_num) (B 92603 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109755 : Reach 109755 := (sr 1 109755 164633 (by norm_num) (by norm_num) (sr 2 164633 123475 (by norm_num) (by norm_num) (sr 1 123475 185213 (by norm_num) (by norm_num) (sr 3 185213 69455 (by norm_num) (by norm_num) (B 69455 (by norm_num) (by norm_num) (by norm_num))))))
theorem R109759 : Reach 109759 := (sr 1 109759 164639 (by norm_num) (by norm_num) (sr 1 164639 246959 (by norm_num) (by norm_num) (sr 1 246959 370439 (by norm_num) (by norm_num) (sr 1 370439 555659 (by norm_num) (by norm_num) (sr 1 555659 833489 (by norm_num) (by norm_num) (sr 2 833489 625117 (by norm_num) (by norm_num) (sr 3 625117 234419 (by norm_num) (by norm_num) (sr 1 234419 351629 (by norm_num) (by norm_num) (sr 3 351629 131861 (by norm_num) (by norm_num) (sr 6 131861 6181 (by norm_num) (by norm_num) (B 6181 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R109763 : Reach 109763 := (sr 1 109763 164645 (by norm_num) (by norm_num) (sr 4 164645 30871 (by norm_num) (by norm_num) (B 30871 (by norm_num) (by norm_num) (by norm_num))))
theorem R109767 : Reach 109767 := (sr 1 109767 164651 (by norm_num) (by norm_num) (sr 1 164651 246977 (by norm_num) (by norm_num) (sr 2 246977 185233 (by norm_num) (by norm_num) (sr 2 185233 138925 (by norm_num) (by norm_num) (sr 3 138925 52097 (by norm_num) (by norm_num) (B 52097 (by norm_num) (by norm_num) (by norm_num)))))))
theorem R109771 : Reach 109771 := (sr 1 109771 164657 (by norm_num) (by norm_num) (sr 2 164657 123493 (by norm_num) (by norm_num) (sr 4 123493 23155 (by norm_num) (by norm_num) (B 23155 (by norm_num) (by norm_num) (by norm_num)))))
theorem R109775 : Reach 109775 := (sr 1 109775 164663 (by norm_num) (by norm_num) (sr 1 164663 246995 (by norm_num) (by norm_num) (sr 1 246995 370493 (by norm_num) (by norm_num) (sr 3 370493 138935 (by norm_num) (by norm_num) (sr 1 138935 208403 (by norm_num) (by norm_num) (sr 1 208403 312605 (by norm_num) (by norm_num) (sr 3 312605 117227 (by norm_num) (by norm_num) (sr 1 117227 175841 (by norm_num) (by norm_num) (sr 2 175841 131881 (by norm_num) (by norm_num) (sr 2 131881 98911 (by norm_num) (by norm_num) (B 98911 (by norm_num) (by norm_num) (by norm_num))))))))))))
theorem R109779 : Reach 109779 := (sr 1 109779 164669 (by norm_num) (by norm_num) (sr 3 164669 61751 (by norm_num) (by norm_num) (B 61751 (by norm_num) (by norm_num) (by norm_num))))

theorem key : ∀ m : ℕ, 0 < m → Odd m → m < 109781 → Reach m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hodd hlt
    rcases Nat.lt_or_ge m 99781 with hlo | hlo
    · exact B m hm (Nat.odd_iff.mp hodd) hlo
    · have hodd' : m % 2 = 1 := Nat.odd_iff.mp hodd
      have hcase : m % 4 = 1 ∨ m % 4 = 3 := by omega
      rcases hcase with h1 | h3
      · exact rs rfl (ih (syracuseStep m) (stepLt (by omega) h1) (stepPos m) (stepOdd m)
          (by have := stepLt (show 1 < m by omega) h1; omega))
      · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
        have hj1 : 24945 ≤ j := by omega
        have hj2 : j ≤ 27444 := by omega
        clear ih hm hodd hodd' h3 hlo hlt
        interval_cases j
        · exact R99783
        · exact R99787
        · exact R99791
        · exact R99795
        · exact R99799
        · exact R99803
        · exact R99807
        · exact R99811
        · exact R99815
        · exact R99819
        · exact R99823
        · exact R99827
        · exact R99831
        · exact R99835
        · exact R99839
        · exact R99843
        · exact R99847
        · exact R99851
        · exact R99855
        · exact R99859
        · exact R99863
        · exact R99867
        · exact R99871
        · exact R99875
        · exact R99879
        · exact R99883
        · exact R99887
        · exact R99891
        · exact R99895
        · exact R99899
        · exact R99903
        · exact R99907
        · exact R99911
        · exact R99915
        · exact R99919
        · exact R99923
        · exact R99927
        · exact R99931
        · exact R99935
        · exact R99939
        · exact R99943
        · exact R99947
        · exact R99951
        · exact R99955
        · exact R99959
        · exact R99963
        · exact R99967
        · exact R99971
        · exact R99975
        · exact R99979
        · exact R99983
        · exact R99987
        · exact R99991
        · exact R99995
        · exact R99999
        · exact R100003
        · exact R100007
        · exact R100011
        · exact R100015
        · exact R100019
        · exact R100023
        · exact R100027
        · exact R100031
        · exact R100035
        · exact R100039
        · exact R100043
        · exact R100047
        · exact R100051
        · exact R100055
        · exact R100059
        · exact R100063
        · exact R100067
        · exact R100071
        · exact R100075
        · exact R100079
        · exact R100083
        · exact R100087
        · exact R100091
        · exact R100095
        · exact R100099
        · exact R100103
        · exact R100107
        · exact R100111
        · exact R100115
        · exact R100119
        · exact R100123
        · exact R100127
        · exact R100131
        · exact R100135
        · exact R100139
        · exact R100143
        · exact R100147
        · exact R100151
        · exact R100155
        · exact R100159
        · exact R100163
        · exact R100167
        · exact R100171
        · exact R100175
        · exact R100179
        · exact R100183
        · exact R100187
        · exact R100191
        · exact R100195
        · exact R100199
        · exact R100203
        · exact R100207
        · exact R100211
        · exact R100215
        · exact R100219
        · exact R100223
        · exact R100227
        · exact R100231
        · exact R100235
        · exact R100239
        · exact R100243
        · exact R100247
        · exact R100251
        · exact R100255
        · exact R100259
        · exact R100263
        · exact R100267
        · exact R100271
        · exact R100275
        · exact R100279
        · exact R100283
        · exact R100287
        · exact R100291
        · exact R100295
        · exact R100299
        · exact R100303
        · exact R100307
        · exact R100311
        · exact R100315
        · exact R100319
        · exact R100323
        · exact R100327
        · exact R100331
        · exact R100335
        · exact R100339
        · exact R100343
        · exact R100347
        · exact R100351
        · exact R100355
        · exact R100359
        · exact R100363
        · exact R100367
        · exact R100371
        · exact R100375
        · exact R100379
        · exact R100383
        · exact R100387
        · exact R100391
        · exact R100395
        · exact R100399
        · exact R100403
        · exact R100407
        · exact R100411
        · exact R100415
        · exact R100419
        · exact R100423
        · exact R100427
        · exact R100431
        · exact R100435
        · exact R100439
        · exact R100443
        · exact R100447
        · exact R100451
        · exact R100455
        · exact R100459
        · exact R100463
        · exact R100467
        · exact R100471
        · exact R100475
        · exact R100479
        · exact R100483
        · exact R100487
        · exact R100491
        · exact R100495
        · exact R100499
        · exact R100503
        · exact R100507
        · exact R100511
        · exact R100515
        · exact R100519
        · exact R100523
        · exact R100527
        · exact R100531
        · exact R100535
        · exact R100539
        · exact R100543
        · exact R100547
        · exact R100551
        · exact R100555
        · exact R100559
        · exact R100563
        · exact R100567
        · exact R100571
        · exact R100575
        · exact R100579
        · exact R100583
        · exact R100587
        · exact R100591
        · exact R100595
        · exact R100599
        · exact R100603
        · exact R100607
        · exact R100611
        · exact R100615
        · exact R100619
        · exact R100623
        · exact R100627
        · exact R100631
        · exact R100635
        · exact R100639
        · exact R100643
        · exact R100647
        · exact R100651
        · exact R100655
        · exact R100659
        · exact R100663
        · exact R100667
        · exact R100671
        · exact R100675
        · exact R100679
        · exact R100683
        · exact R100687
        · exact R100691
        · exact R100695
        · exact R100699
        · exact R100703
        · exact R100707
        · exact R100711
        · exact R100715
        · exact R100719
        · exact R100723
        · exact R100727
        · exact R100731
        · exact R100735
        · exact R100739
        · exact R100743
        · exact R100747
        · exact R100751
        · exact R100755
        · exact R100759
        · exact R100763
        · exact R100767
        · exact R100771
        · exact R100775
        · exact R100779
        · exact R100783
        · exact R100787
        · exact R100791
        · exact R100795
        · exact R100799
        · exact R100803
        · exact R100807
        · exact R100811
        · exact R100815
        · exact R100819
        · exact R100823
        · exact R100827
        · exact R100831
        · exact R100835
        · exact R100839
        · exact R100843
        · exact R100847
        · exact R100851
        · exact R100855
        · exact R100859
        · exact R100863
        · exact R100867
        · exact R100871
        · exact R100875
        · exact R100879
        · exact R100883
        · exact R100887
        · exact R100891
        · exact R100895
        · exact R100899
        · exact R100903
        · exact R100907
        · exact R100911
        · exact R100915
        · exact R100919
        · exact R100923
        · exact R100927
        · exact R100931
        · exact R100935
        · exact R100939
        · exact R100943
        · exact R100947
        · exact R100951
        · exact R100955
        · exact R100959
        · exact R100963
        · exact R100967
        · exact R100971
        · exact R100975
        · exact R100979
        · exact R100983
        · exact R100987
        · exact R100991
        · exact R100995
        · exact R100999
        · exact R101003
        · exact R101007
        · exact R101011
        · exact R101015
        · exact R101019
        · exact R101023
        · exact R101027
        · exact R101031
        · exact R101035
        · exact R101039
        · exact R101043
        · exact R101047
        · exact R101051
        · exact R101055
        · exact R101059
        · exact R101063
        · exact R101067
        · exact R101071
        · exact R101075
        · exact R101079
        · exact R101083
        · exact R101087
        · exact R101091
        · exact R101095
        · exact R101099
        · exact R101103
        · exact R101107
        · exact R101111
        · exact R101115
        · exact R101119
        · exact R101123
        · exact R101127
        · exact R101131
        · exact R101135
        · exact R101139
        · exact R101143
        · exact R101147
        · exact R101151
        · exact R101155
        · exact R101159
        · exact R101163
        · exact R101167
        · exact R101171
        · exact R101175
        · exact R101179
        · exact R101183
        · exact R101187
        · exact R101191
        · exact R101195
        · exact R101199
        · exact R101203
        · exact R101207
        · exact R101211
        · exact R101215
        · exact R101219
        · exact R101223
        · exact R101227
        · exact R101231
        · exact R101235
        · exact R101239
        · exact R101243
        · exact R101247
        · exact R101251
        · exact R101255
        · exact R101259
        · exact R101263
        · exact R101267
        · exact R101271
        · exact R101275
        · exact R101279
        · exact R101283
        · exact R101287
        · exact R101291
        · exact R101295
        · exact R101299
        · exact R101303
        · exact R101307
        · exact R101311
        · exact R101315
        · exact R101319
        · exact R101323
        · exact R101327
        · exact R101331
        · exact R101335
        · exact R101339
        · exact R101343
        · exact R101347
        · exact R101351
        · exact R101355
        · exact R101359
        · exact R101363
        · exact R101367
        · exact R101371
        · exact R101375
        · exact R101379
        · exact R101383
        · exact R101387
        · exact R101391
        · exact R101395
        · exact R101399
        · exact R101403
        · exact R101407
        · exact R101411
        · exact R101415
        · exact R101419
        · exact R101423
        · exact R101427
        · exact R101431
        · exact R101435
        · exact R101439
        · exact R101443
        · exact R101447
        · exact R101451
        · exact R101455
        · exact R101459
        · exact R101463
        · exact R101467
        · exact R101471
        · exact R101475
        · exact R101479
        · exact R101483
        · exact R101487
        · exact R101491
        · exact R101495
        · exact R101499
        · exact R101503
        · exact R101507
        · exact R101511
        · exact R101515
        · exact R101519
        · exact R101523
        · exact R101527
        · exact R101531
        · exact R101535
        · exact R101539
        · exact R101543
        · exact R101547
        · exact R101551
        · exact R101555
        · exact R101559
        · exact R101563
        · exact R101567
        · exact R101571
        · exact R101575
        · exact R101579
        · exact R101583
        · exact R101587
        · exact R101591
        · exact R101595
        · exact R101599
        · exact R101603
        · exact R101607
        · exact R101611
        · exact R101615
        · exact R101619
        · exact R101623
        · exact R101627
        · exact R101631
        · exact R101635
        · exact R101639
        · exact R101643
        · exact R101647
        · exact R101651
        · exact R101655
        · exact R101659
        · exact R101663
        · exact R101667
        · exact R101671
        · exact R101675
        · exact R101679
        · exact R101683
        · exact R101687
        · exact R101691
        · exact R101695
        · exact R101699
        · exact R101703
        · exact R101707
        · exact R101711
        · exact R101715
        · exact R101719
        · exact R101723
        · exact R101727
        · exact R101731
        · exact R101735
        · exact R101739
        · exact R101743
        · exact R101747
        · exact R101751
        · exact R101755
        · exact R101759
        · exact R101763
        · exact R101767
        · exact R101771
        · exact R101775
        · exact R101779
        · exact R101783
        · exact R101787
        · exact R101791
        · exact R101795
        · exact R101799
        · exact R101803
        · exact R101807
        · exact R101811
        · exact R101815
        · exact R101819
        · exact R101823
        · exact R101827
        · exact R101831
        · exact R101835
        · exact R101839
        · exact R101843
        · exact R101847
        · exact R101851
        · exact R101855
        · exact R101859
        · exact R101863
        · exact R101867
        · exact R101871
        · exact R101875
        · exact R101879
        · exact R101883
        · exact R101887
        · exact R101891
        · exact R101895
        · exact R101899
        · exact R101903
        · exact R101907
        · exact R101911
        · exact R101915
        · exact R101919
        · exact R101923
        · exact R101927
        · exact R101931
        · exact R101935
        · exact R101939
        · exact R101943
        · exact R101947
        · exact R101951
        · exact R101955
        · exact R101959
        · exact R101963
        · exact R101967
        · exact R101971
        · exact R101975
        · exact R101979
        · exact R101983
        · exact R101987
        · exact R101991
        · exact R101995
        · exact R101999
        · exact R102003
        · exact R102007
        · exact R102011
        · exact R102015
        · exact R102019
        · exact R102023
        · exact R102027
        · exact R102031
        · exact R102035
        · exact R102039
        · exact R102043
        · exact R102047
        · exact R102051
        · exact R102055
        · exact R102059
        · exact R102063
        · exact R102067
        · exact R102071
        · exact R102075
        · exact R102079
        · exact R102083
        · exact R102087
        · exact R102091
        · exact R102095
        · exact R102099
        · exact R102103
        · exact R102107
        · exact R102111
        · exact R102115
        · exact R102119
        · exact R102123
        · exact R102127
        · exact R102131
        · exact R102135
        · exact R102139
        · exact R102143
        · exact R102147
        · exact R102151
        · exact R102155
        · exact R102159
        · exact R102163
        · exact R102167
        · exact R102171
        · exact R102175
        · exact R102179
        · exact R102183
        · exact R102187
        · exact R102191
        · exact R102195
        · exact R102199
        · exact R102203
        · exact R102207
        · exact R102211
        · exact R102215
        · exact R102219
        · exact R102223
        · exact R102227
        · exact R102231
        · exact R102235
        · exact R102239
        · exact R102243
        · exact R102247
        · exact R102251
        · exact R102255
        · exact R102259
        · exact R102263
        · exact R102267
        · exact R102271
        · exact R102275
        · exact R102279
        · exact R102283
        · exact R102287
        · exact R102291
        · exact R102295
        · exact R102299
        · exact R102303
        · exact R102307
        · exact R102311
        · exact R102315
        · exact R102319
        · exact R102323
        · exact R102327
        · exact R102331
        · exact R102335
        · exact R102339
        · exact R102343
        · exact R102347
        · exact R102351
        · exact R102355
        · exact R102359
        · exact R102363
        · exact R102367
        · exact R102371
        · exact R102375
        · exact R102379
        · exact R102383
        · exact R102387
        · exact R102391
        · exact R102395
        · exact R102399
        · exact R102403
        · exact R102407
        · exact R102411
        · exact R102415
        · exact R102419
        · exact R102423
        · exact R102427
        · exact R102431
        · exact R102435
        · exact R102439
        · exact R102443
        · exact R102447
        · exact R102451
        · exact R102455
        · exact R102459
        · exact R102463
        · exact R102467
        · exact R102471
        · exact R102475
        · exact R102479
        · exact R102483
        · exact R102487
        · exact R102491
        · exact R102495
        · exact R102499
        · exact R102503
        · exact R102507
        · exact R102511
        · exact R102515
        · exact R102519
        · exact R102523
        · exact R102527
        · exact R102531
        · exact R102535
        · exact R102539
        · exact R102543
        · exact R102547
        · exact R102551
        · exact R102555
        · exact R102559
        · exact R102563
        · exact R102567
        · exact R102571
        · exact R102575
        · exact R102579
        · exact R102583
        · exact R102587
        · exact R102591
        · exact R102595
        · exact R102599
        · exact R102603
        · exact R102607
        · exact R102611
        · exact R102615
        · exact R102619
        · exact R102623
        · exact R102627
        · exact R102631
        · exact R102635
        · exact R102639
        · exact R102643
        · exact R102647
        · exact R102651
        · exact R102655
        · exact R102659
        · exact R102663
        · exact R102667
        · exact R102671
        · exact R102675
        · exact R102679
        · exact R102683
        · exact R102687
        · exact R102691
        · exact R102695
        · exact R102699
        · exact R102703
        · exact R102707
        · exact R102711
        · exact R102715
        · exact R102719
        · exact R102723
        · exact R102727
        · exact R102731
        · exact R102735
        · exact R102739
        · exact R102743
        · exact R102747
        · exact R102751
        · exact R102755
        · exact R102759
        · exact R102763
        · exact R102767
        · exact R102771
        · exact R102775
        · exact R102779
        · exact R102783
        · exact R102787
        · exact R102791
        · exact R102795
        · exact R102799
        · exact R102803
        · exact R102807
        · exact R102811
        · exact R102815
        · exact R102819
        · exact R102823
        · exact R102827
        · exact R102831
        · exact R102835
        · exact R102839
        · exact R102843
        · exact R102847
        · exact R102851
        · exact R102855
        · exact R102859
        · exact R102863
        · exact R102867
        · exact R102871
        · exact R102875
        · exact R102879
        · exact R102883
        · exact R102887
        · exact R102891
        · exact R102895
        · exact R102899
        · exact R102903
        · exact R102907
        · exact R102911
        · exact R102915
        · exact R102919
        · exact R102923
        · exact R102927
        · exact R102931
        · exact R102935
        · exact R102939
        · exact R102943
        · exact R102947
        · exact R102951
        · exact R102955
        · exact R102959
        · exact R102963
        · exact R102967
        · exact R102971
        · exact R102975
        · exact R102979
        · exact R102983
        · exact R102987
        · exact R102991
        · exact R102995
        · exact R102999
        · exact R103003
        · exact R103007
        · exact R103011
        · exact R103015
        · exact R103019
        · exact R103023
        · exact R103027
        · exact R103031
        · exact R103035
        · exact R103039
        · exact R103043
        · exact R103047
        · exact R103051
        · exact R103055
        · exact R103059
        · exact R103063
        · exact R103067
        · exact R103071
        · exact R103075
        · exact R103079
        · exact R103083
        · exact R103087
        · exact R103091
        · exact R103095
        · exact R103099
        · exact R103103
        · exact R103107
        · exact R103111
        · exact R103115
        · exact R103119
        · exact R103123
        · exact R103127
        · exact R103131
        · exact R103135
        · exact R103139
        · exact R103143
        · exact R103147
        · exact R103151
        · exact R103155
        · exact R103159
        · exact R103163
        · exact R103167
        · exact R103171
        · exact R103175
        · exact R103179
        · exact R103183
        · exact R103187
        · exact R103191
        · exact R103195
        · exact R103199
        · exact R103203
        · exact R103207
        · exact R103211
        · exact R103215
        · exact R103219
        · exact R103223
        · exact R103227
        · exact R103231
        · exact R103235
        · exact R103239
        · exact R103243
        · exact R103247
        · exact R103251
        · exact R103255
        · exact R103259
        · exact R103263
        · exact R103267
        · exact R103271
        · exact R103275
        · exact R103279
        · exact R103283
        · exact R103287
        · exact R103291
        · exact R103295
        · exact R103299
        · exact R103303
        · exact R103307
        · exact R103311
        · exact R103315
        · exact R103319
        · exact R103323
        · exact R103327
        · exact R103331
        · exact R103335
        · exact R103339
        · exact R103343
        · exact R103347
        · exact R103351
        · exact R103355
        · exact R103359
        · exact R103363
        · exact R103367
        · exact R103371
        · exact R103375
        · exact R103379
        · exact R103383
        · exact R103387
        · exact R103391
        · exact R103395
        · exact R103399
        · exact R103403
        · exact R103407
        · exact R103411
        · exact R103415
        · exact R103419
        · exact R103423
        · exact R103427
        · exact R103431
        · exact R103435
        · exact R103439
        · exact R103443
        · exact R103447
        · exact R103451
        · exact R103455
        · exact R103459
        · exact R103463
        · exact R103467
        · exact R103471
        · exact R103475
        · exact R103479
        · exact R103483
        · exact R103487
        · exact R103491
        · exact R103495
        · exact R103499
        · exact R103503
        · exact R103507
        · exact R103511
        · exact R103515
        · exact R103519
        · exact R103523
        · exact R103527
        · exact R103531
        · exact R103535
        · exact R103539
        · exact R103543
        · exact R103547
        · exact R103551
        · exact R103555
        · exact R103559
        · exact R103563
        · exact R103567
        · exact R103571
        · exact R103575
        · exact R103579
        · exact R103583
        · exact R103587
        · exact R103591
        · exact R103595
        · exact R103599
        · exact R103603
        · exact R103607
        · exact R103611
        · exact R103615
        · exact R103619
        · exact R103623
        · exact R103627
        · exact R103631
        · exact R103635
        · exact R103639
        · exact R103643
        · exact R103647
        · exact R103651
        · exact R103655
        · exact R103659
        · exact R103663
        · exact R103667
        · exact R103671
        · exact R103675
        · exact R103679
        · exact R103683
        · exact R103687
        · exact R103691
        · exact R103695
        · exact R103699
        · exact R103703
        · exact R103707
        · exact R103711
        · exact R103715
        · exact R103719
        · exact R103723
        · exact R103727
        · exact R103731
        · exact R103735
        · exact R103739
        · exact R103743
        · exact R103747
        · exact R103751
        · exact R103755
        · exact R103759
        · exact R103763
        · exact R103767
        · exact R103771
        · exact R103775
        · exact R103779
        · exact R103783
        · exact R103787
        · exact R103791
        · exact R103795
        · exact R103799
        · exact R103803
        · exact R103807
        · exact R103811
        · exact R103815
        · exact R103819
        · exact R103823
        · exact R103827
        · exact R103831
        · exact R103835
        · exact R103839
        · exact R103843
        · exact R103847
        · exact R103851
        · exact R103855
        · exact R103859
        · exact R103863
        · exact R103867
        · exact R103871
        · exact R103875
        · exact R103879
        · exact R103883
        · exact R103887
        · exact R103891
        · exact R103895
        · exact R103899
        · exact R103903
        · exact R103907
        · exact R103911
        · exact R103915
        · exact R103919
        · exact R103923
        · exact R103927
        · exact R103931
        · exact R103935
        · exact R103939
        · exact R103943
        · exact R103947
        · exact R103951
        · exact R103955
        · exact R103959
        · exact R103963
        · exact R103967
        · exact R103971
        · exact R103975
        · exact R103979
        · exact R103983
        · exact R103987
        · exact R103991
        · exact R103995
        · exact R103999
        · exact R104003
        · exact R104007
        · exact R104011
        · exact R104015
        · exact R104019
        · exact R104023
        · exact R104027
        · exact R104031
        · exact R104035
        · exact R104039
        · exact R104043
        · exact R104047
        · exact R104051
        · exact R104055
        · exact R104059
        · exact R104063
        · exact R104067
        · exact R104071
        · exact R104075
        · exact R104079
        · exact R104083
        · exact R104087
        · exact R104091
        · exact R104095
        · exact R104099
        · exact R104103
        · exact R104107
        · exact R104111
        · exact R104115
        · exact R104119
        · exact R104123
        · exact R104127
        · exact R104131
        · exact R104135
        · exact R104139
        · exact R104143
        · exact R104147
        · exact R104151
        · exact R104155
        · exact R104159
        · exact R104163
        · exact R104167
        · exact R104171
        · exact R104175
        · exact R104179
        · exact R104183
        · exact R104187
        · exact R104191
        · exact R104195
        · exact R104199
        · exact R104203
        · exact R104207
        · exact R104211
        · exact R104215
        · exact R104219
        · exact R104223
        · exact R104227
        · exact R104231
        · exact R104235
        · exact R104239
        · exact R104243
        · exact R104247
        · exact R104251
        · exact R104255
        · exact R104259
        · exact R104263
        · exact R104267
        · exact R104271
        · exact R104275
        · exact R104279
        · exact R104283
        · exact R104287
        · exact R104291
        · exact R104295
        · exact R104299
        · exact R104303
        · exact R104307
        · exact R104311
        · exact R104315
        · exact R104319
        · exact R104323
        · exact R104327
        · exact R104331
        · exact R104335
        · exact R104339
        · exact R104343
        · exact R104347
        · exact R104351
        · exact R104355
        · exact R104359
        · exact R104363
        · exact R104367
        · exact R104371
        · exact R104375
        · exact R104379
        · exact R104383
        · exact R104387
        · exact R104391
        · exact R104395
        · exact R104399
        · exact R104403
        · exact R104407
        · exact R104411
        · exact R104415
        · exact R104419
        · exact R104423
        · exact R104427
        · exact R104431
        · exact R104435
        · exact R104439
        · exact R104443
        · exact R104447
        · exact R104451
        · exact R104455
        · exact R104459
        · exact R104463
        · exact R104467
        · exact R104471
        · exact R104475
        · exact R104479
        · exact R104483
        · exact R104487
        · exact R104491
        · exact R104495
        · exact R104499
        · exact R104503
        · exact R104507
        · exact R104511
        · exact R104515
        · exact R104519
        · exact R104523
        · exact R104527
        · exact R104531
        · exact R104535
        · exact R104539
        · exact R104543
        · exact R104547
        · exact R104551
        · exact R104555
        · exact R104559
        · exact R104563
        · exact R104567
        · exact R104571
        · exact R104575
        · exact R104579
        · exact R104583
        · exact R104587
        · exact R104591
        · exact R104595
        · exact R104599
        · exact R104603
        · exact R104607
        · exact R104611
        · exact R104615
        · exact R104619
        · exact R104623
        · exact R104627
        · exact R104631
        · exact R104635
        · exact R104639
        · exact R104643
        · exact R104647
        · exact R104651
        · exact R104655
        · exact R104659
        · exact R104663
        · exact R104667
        · exact R104671
        · exact R104675
        · exact R104679
        · exact R104683
        · exact R104687
        · exact R104691
        · exact R104695
        · exact R104699
        · exact R104703
        · exact R104707
        · exact R104711
        · exact R104715
        · exact R104719
        · exact R104723
        · exact R104727
        · exact R104731
        · exact R104735
        · exact R104739
        · exact R104743
        · exact R104747
        · exact R104751
        · exact R104755
        · exact R104759
        · exact R104763
        · exact R104767
        · exact R104771
        · exact R104775
        · exact R104779
        · exact R104783
        · exact R104787
        · exact R104791
        · exact R104795
        · exact R104799
        · exact R104803
        · exact R104807
        · exact R104811
        · exact R104815
        · exact R104819
        · exact R104823
        · exact R104827
        · exact R104831
        · exact R104835
        · exact R104839
        · exact R104843
        · exact R104847
        · exact R104851
        · exact R104855
        · exact R104859
        · exact R104863
        · exact R104867
        · exact R104871
        · exact R104875
        · exact R104879
        · exact R104883
        · exact R104887
        · exact R104891
        · exact R104895
        · exact R104899
        · exact R104903
        · exact R104907
        · exact R104911
        · exact R104915
        · exact R104919
        · exact R104923
        · exact R104927
        · exact R104931
        · exact R104935
        · exact R104939
        · exact R104943
        · exact R104947
        · exact R104951
        · exact R104955
        · exact R104959
        · exact R104963
        · exact R104967
        · exact R104971
        · exact R104975
        · exact R104979
        · exact R104983
        · exact R104987
        · exact R104991
        · exact R104995
        · exact R104999
        · exact R105003
        · exact R105007
        · exact R105011
        · exact R105015
        · exact R105019
        · exact R105023
        · exact R105027
        · exact R105031
        · exact R105035
        · exact R105039
        · exact R105043
        · exact R105047
        · exact R105051
        · exact R105055
        · exact R105059
        · exact R105063
        · exact R105067
        · exact R105071
        · exact R105075
        · exact R105079
        · exact R105083
        · exact R105087
        · exact R105091
        · exact R105095
        · exact R105099
        · exact R105103
        · exact R105107
        · exact R105111
        · exact R105115
        · exact R105119
        · exact R105123
        · exact R105127
        · exact R105131
        · exact R105135
        · exact R105139
        · exact R105143
        · exact R105147
        · exact R105151
        · exact R105155
        · exact R105159
        · exact R105163
        · exact R105167
        · exact R105171
        · exact R105175
        · exact R105179
        · exact R105183
        · exact R105187
        · exact R105191
        · exact R105195
        · exact R105199
        · exact R105203
        · exact R105207
        · exact R105211
        · exact R105215
        · exact R105219
        · exact R105223
        · exact R105227
        · exact R105231
        · exact R105235
        · exact R105239
        · exact R105243
        · exact R105247
        · exact R105251
        · exact R105255
        · exact R105259
        · exact R105263
        · exact R105267
        · exact R105271
        · exact R105275
        · exact R105279
        · exact R105283
        · exact R105287
        · exact R105291
        · exact R105295
        · exact R105299
        · exact R105303
        · exact R105307
        · exact R105311
        · exact R105315
        · exact R105319
        · exact R105323
        · exact R105327
        · exact R105331
        · exact R105335
        · exact R105339
        · exact R105343
        · exact R105347
        · exact R105351
        · exact R105355
        · exact R105359
        · exact R105363
        · exact R105367
        · exact R105371
        · exact R105375
        · exact R105379
        · exact R105383
        · exact R105387
        · exact R105391
        · exact R105395
        · exact R105399
        · exact R105403
        · exact R105407
        · exact R105411
        · exact R105415
        · exact R105419
        · exact R105423
        · exact R105427
        · exact R105431
        · exact R105435
        · exact R105439
        · exact R105443
        · exact R105447
        · exact R105451
        · exact R105455
        · exact R105459
        · exact R105463
        · exact R105467
        · exact R105471
        · exact R105475
        · exact R105479
        · exact R105483
        · exact R105487
        · exact R105491
        · exact R105495
        · exact R105499
        · exact R105503
        · exact R105507
        · exact R105511
        · exact R105515
        · exact R105519
        · exact R105523
        · exact R105527
        · exact R105531
        · exact R105535
        · exact R105539
        · exact R105543
        · exact R105547
        · exact R105551
        · exact R105555
        · exact R105559
        · exact R105563
        · exact R105567
        · exact R105571
        · exact R105575
        · exact R105579
        · exact R105583
        · exact R105587
        · exact R105591
        · exact R105595
        · exact R105599
        · exact R105603
        · exact R105607
        · exact R105611
        · exact R105615
        · exact R105619
        · exact R105623
        · exact R105627
        · exact R105631
        · exact R105635
        · exact R105639
        · exact R105643
        · exact R105647
        · exact R105651
        · exact R105655
        · exact R105659
        · exact R105663
        · exact R105667
        · exact R105671
        · exact R105675
        · exact R105679
        · exact R105683
        · exact R105687
        · exact R105691
        · exact R105695
        · exact R105699
        · exact R105703
        · exact R105707
        · exact R105711
        · exact R105715
        · exact R105719
        · exact R105723
        · exact R105727
        · exact R105731
        · exact R105735
        · exact R105739
        · exact R105743
        · exact R105747
        · exact R105751
        · exact R105755
        · exact R105759
        · exact R105763
        · exact R105767
        · exact R105771
        · exact R105775
        · exact R105779
        · exact R105783
        · exact R105787
        · exact R105791
        · exact R105795
        · exact R105799
        · exact R105803
        · exact R105807
        · exact R105811
        · exact R105815
        · exact R105819
        · exact R105823
        · exact R105827
        · exact R105831
        · exact R105835
        · exact R105839
        · exact R105843
        · exact R105847
        · exact R105851
        · exact R105855
        · exact R105859
        · exact R105863
        · exact R105867
        · exact R105871
        · exact R105875
        · exact R105879
        · exact R105883
        · exact R105887
        · exact R105891
        · exact R105895
        · exact R105899
        · exact R105903
        · exact R105907
        · exact R105911
        · exact R105915
        · exact R105919
        · exact R105923
        · exact R105927
        · exact R105931
        · exact R105935
        · exact R105939
        · exact R105943
        · exact R105947
        · exact R105951
        · exact R105955
        · exact R105959
        · exact R105963
        · exact R105967
        · exact R105971
        · exact R105975
        · exact R105979
        · exact R105983
        · exact R105987
        · exact R105991
        · exact R105995
        · exact R105999
        · exact R106003
        · exact R106007
        · exact R106011
        · exact R106015
        · exact R106019
        · exact R106023
        · exact R106027
        · exact R106031
        · exact R106035
        · exact R106039
        · exact R106043
        · exact R106047
        · exact R106051
        · exact R106055
        · exact R106059
        · exact R106063
        · exact R106067
        · exact R106071
        · exact R106075
        · exact R106079
        · exact R106083
        · exact R106087
        · exact R106091
        · exact R106095
        · exact R106099
        · exact R106103
        · exact R106107
        · exact R106111
        · exact R106115
        · exact R106119
        · exact R106123
        · exact R106127
        · exact R106131
        · exact R106135
        · exact R106139
        · exact R106143
        · exact R106147
        · exact R106151
        · exact R106155
        · exact R106159
        · exact R106163
        · exact R106167
        · exact R106171
        · exact R106175
        · exact R106179
        · exact R106183
        · exact R106187
        · exact R106191
        · exact R106195
        · exact R106199
        · exact R106203
        · exact R106207
        · exact R106211
        · exact R106215
        · exact R106219
        · exact R106223
        · exact R106227
        · exact R106231
        · exact R106235
        · exact R106239
        · exact R106243
        · exact R106247
        · exact R106251
        · exact R106255
        · exact R106259
        · exact R106263
        · exact R106267
        · exact R106271
        · exact R106275
        · exact R106279
        · exact R106283
        · exact R106287
        · exact R106291
        · exact R106295
        · exact R106299
        · exact R106303
        · exact R106307
        · exact R106311
        · exact R106315
        · exact R106319
        · exact R106323
        · exact R106327
        · exact R106331
        · exact R106335
        · exact R106339
        · exact R106343
        · exact R106347
        · exact R106351
        · exact R106355
        · exact R106359
        · exact R106363
        · exact R106367
        · exact R106371
        · exact R106375
        · exact R106379
        · exact R106383
        · exact R106387
        · exact R106391
        · exact R106395
        · exact R106399
        · exact R106403
        · exact R106407
        · exact R106411
        · exact R106415
        · exact R106419
        · exact R106423
        · exact R106427
        · exact R106431
        · exact R106435
        · exact R106439
        · exact R106443
        · exact R106447
        · exact R106451
        · exact R106455
        · exact R106459
        · exact R106463
        · exact R106467
        · exact R106471
        · exact R106475
        · exact R106479
        · exact R106483
        · exact R106487
        · exact R106491
        · exact R106495
        · exact R106499
        · exact R106503
        · exact R106507
        · exact R106511
        · exact R106515
        · exact R106519
        · exact R106523
        · exact R106527
        · exact R106531
        · exact R106535
        · exact R106539
        · exact R106543
        · exact R106547
        · exact R106551
        · exact R106555
        · exact R106559
        · exact R106563
        · exact R106567
        · exact R106571
        · exact R106575
        · exact R106579
        · exact R106583
        · exact R106587
        · exact R106591
        · exact R106595
        · exact R106599
        · exact R106603
        · exact R106607
        · exact R106611
        · exact R106615
        · exact R106619
        · exact R106623
        · exact R106627
        · exact R106631
        · exact R106635
        · exact R106639
        · exact R106643
        · exact R106647
        · exact R106651
        · exact R106655
        · exact R106659
        · exact R106663
        · exact R106667
        · exact R106671
        · exact R106675
        · exact R106679
        · exact R106683
        · exact R106687
        · exact R106691
        · exact R106695
        · exact R106699
        · exact R106703
        · exact R106707
        · exact R106711
        · exact R106715
        · exact R106719
        · exact R106723
        · exact R106727
        · exact R106731
        · exact R106735
        · exact R106739
        · exact R106743
        · exact R106747
        · exact R106751
        · exact R106755
        · exact R106759
        · exact R106763
        · exact R106767
        · exact R106771
        · exact R106775
        · exact R106779
        · exact R106783
        · exact R106787
        · exact R106791
        · exact R106795
        · exact R106799
        · exact R106803
        · exact R106807
        · exact R106811
        · exact R106815
        · exact R106819
        · exact R106823
        · exact R106827
        · exact R106831
        · exact R106835
        · exact R106839
        · exact R106843
        · exact R106847
        · exact R106851
        · exact R106855
        · exact R106859
        · exact R106863
        · exact R106867
        · exact R106871
        · exact R106875
        · exact R106879
        · exact R106883
        · exact R106887
        · exact R106891
        · exact R106895
        · exact R106899
        · exact R106903
        · exact R106907
        · exact R106911
        · exact R106915
        · exact R106919
        · exact R106923
        · exact R106927
        · exact R106931
        · exact R106935
        · exact R106939
        · exact R106943
        · exact R106947
        · exact R106951
        · exact R106955
        · exact R106959
        · exact R106963
        · exact R106967
        · exact R106971
        · exact R106975
        · exact R106979
        · exact R106983
        · exact R106987
        · exact R106991
        · exact R106995
        · exact R106999
        · exact R107003
        · exact R107007
        · exact R107011
        · exact R107015
        · exact R107019
        · exact R107023
        · exact R107027
        · exact R107031
        · exact R107035
        · exact R107039
        · exact R107043
        · exact R107047
        · exact R107051
        · exact R107055
        · exact R107059
        · exact R107063
        · exact R107067
        · exact R107071
        · exact R107075
        · exact R107079
        · exact R107083
        · exact R107087
        · exact R107091
        · exact R107095
        · exact R107099
        · exact R107103
        · exact R107107
        · exact R107111
        · exact R107115
        · exact R107119
        · exact R107123
        · exact R107127
        · exact R107131
        · exact R107135
        · exact R107139
        · exact R107143
        · exact R107147
        · exact R107151
        · exact R107155
        · exact R107159
        · exact R107163
        · exact R107167
        · exact R107171
        · exact R107175
        · exact R107179
        · exact R107183
        · exact R107187
        · exact R107191
        · exact R107195
        · exact R107199
        · exact R107203
        · exact R107207
        · exact R107211
        · exact R107215
        · exact R107219
        · exact R107223
        · exact R107227
        · exact R107231
        · exact R107235
        · exact R107239
        · exact R107243
        · exact R107247
        · exact R107251
        · exact R107255
        · exact R107259
        · exact R107263
        · exact R107267
        · exact R107271
        · exact R107275
        · exact R107279
        · exact R107283
        · exact R107287
        · exact R107291
        · exact R107295
        · exact R107299
        · exact R107303
        · exact R107307
        · exact R107311
        · exact R107315
        · exact R107319
        · exact R107323
        · exact R107327
        · exact R107331
        · exact R107335
        · exact R107339
        · exact R107343
        · exact R107347
        · exact R107351
        · exact R107355
        · exact R107359
        · exact R107363
        · exact R107367
        · exact R107371
        · exact R107375
        · exact R107379
        · exact R107383
        · exact R107387
        · exact R107391
        · exact R107395
        · exact R107399
        · exact R107403
        · exact R107407
        · exact R107411
        · exact R107415
        · exact R107419
        · exact R107423
        · exact R107427
        · exact R107431
        · exact R107435
        · exact R107439
        · exact R107443
        · exact R107447
        · exact R107451
        · exact R107455
        · exact R107459
        · exact R107463
        · exact R107467
        · exact R107471
        · exact R107475
        · exact R107479
        · exact R107483
        · exact R107487
        · exact R107491
        · exact R107495
        · exact R107499
        · exact R107503
        · exact R107507
        · exact R107511
        · exact R107515
        · exact R107519
        · exact R107523
        · exact R107527
        · exact R107531
        · exact R107535
        · exact R107539
        · exact R107543
        · exact R107547
        · exact R107551
        · exact R107555
        · exact R107559
        · exact R107563
        · exact R107567
        · exact R107571
        · exact R107575
        · exact R107579
        · exact R107583
        · exact R107587
        · exact R107591
        · exact R107595
        · exact R107599
        · exact R107603
        · exact R107607
        · exact R107611
        · exact R107615
        · exact R107619
        · exact R107623
        · exact R107627
        · exact R107631
        · exact R107635
        · exact R107639
        · exact R107643
        · exact R107647
        · exact R107651
        · exact R107655
        · exact R107659
        · exact R107663
        · exact R107667
        · exact R107671
        · exact R107675
        · exact R107679
        · exact R107683
        · exact R107687
        · exact R107691
        · exact R107695
        · exact R107699
        · exact R107703
        · exact R107707
        · exact R107711
        · exact R107715
        · exact R107719
        · exact R107723
        · exact R107727
        · exact R107731
        · exact R107735
        · exact R107739
        · exact R107743
        · exact R107747
        · exact R107751
        · exact R107755
        · exact R107759
        · exact R107763
        · exact R107767
        · exact R107771
        · exact R107775
        · exact R107779
        · exact R107783
        · exact R107787
        · exact R107791
        · exact R107795
        · exact R107799
        · exact R107803
        · exact R107807
        · exact R107811
        · exact R107815
        · exact R107819
        · exact R107823
        · exact R107827
        · exact R107831
        · exact R107835
        · exact R107839
        · exact R107843
        · exact R107847
        · exact R107851
        · exact R107855
        · exact R107859
        · exact R107863
        · exact R107867
        · exact R107871
        · exact R107875
        · exact R107879
        · exact R107883
        · exact R107887
        · exact R107891
        · exact R107895
        · exact R107899
        · exact R107903
        · exact R107907
        · exact R107911
        · exact R107915
        · exact R107919
        · exact R107923
        · exact R107927
        · exact R107931
        · exact R107935
        · exact R107939
        · exact R107943
        · exact R107947
        · exact R107951
        · exact R107955
        · exact R107959
        · exact R107963
        · exact R107967
        · exact R107971
        · exact R107975
        · exact R107979
        · exact R107983
        · exact R107987
        · exact R107991
        · exact R107995
        · exact R107999
        · exact R108003
        · exact R108007
        · exact R108011
        · exact R108015
        · exact R108019
        · exact R108023
        · exact R108027
        · exact R108031
        · exact R108035
        · exact R108039
        · exact R108043
        · exact R108047
        · exact R108051
        · exact R108055
        · exact R108059
        · exact R108063
        · exact R108067
        · exact R108071
        · exact R108075
        · exact R108079
        · exact R108083
        · exact R108087
        · exact R108091
        · exact R108095
        · exact R108099
        · exact R108103
        · exact R108107
        · exact R108111
        · exact R108115
        · exact R108119
        · exact R108123
        · exact R108127
        · exact R108131
        · exact R108135
        · exact R108139
        · exact R108143
        · exact R108147
        · exact R108151
        · exact R108155
        · exact R108159
        · exact R108163
        · exact R108167
        · exact R108171
        · exact R108175
        · exact R108179
        · exact R108183
        · exact R108187
        · exact R108191
        · exact R108195
        · exact R108199
        · exact R108203
        · exact R108207
        · exact R108211
        · exact R108215
        · exact R108219
        · exact R108223
        · exact R108227
        · exact R108231
        · exact R108235
        · exact R108239
        · exact R108243
        · exact R108247
        · exact R108251
        · exact R108255
        · exact R108259
        · exact R108263
        · exact R108267
        · exact R108271
        · exact R108275
        · exact R108279
        · exact R108283
        · exact R108287
        · exact R108291
        · exact R108295
        · exact R108299
        · exact R108303
        · exact R108307
        · exact R108311
        · exact R108315
        · exact R108319
        · exact R108323
        · exact R108327
        · exact R108331
        · exact R108335
        · exact R108339
        · exact R108343
        · exact R108347
        · exact R108351
        · exact R108355
        · exact R108359
        · exact R108363
        · exact R108367
        · exact R108371
        · exact R108375
        · exact R108379
        · exact R108383
        · exact R108387
        · exact R108391
        · exact R108395
        · exact R108399
        · exact R108403
        · exact R108407
        · exact R108411
        · exact R108415
        · exact R108419
        · exact R108423
        · exact R108427
        · exact R108431
        · exact R108435
        · exact R108439
        · exact R108443
        · exact R108447
        · exact R108451
        · exact R108455
        · exact R108459
        · exact R108463
        · exact R108467
        · exact R108471
        · exact R108475
        · exact R108479
        · exact R108483
        · exact R108487
        · exact R108491
        · exact R108495
        · exact R108499
        · exact R108503
        · exact R108507
        · exact R108511
        · exact R108515
        · exact R108519
        · exact R108523
        · exact R108527
        · exact R108531
        · exact R108535
        · exact R108539
        · exact R108543
        · exact R108547
        · exact R108551
        · exact R108555
        · exact R108559
        · exact R108563
        · exact R108567
        · exact R108571
        · exact R108575
        · exact R108579
        · exact R108583
        · exact R108587
        · exact R108591
        · exact R108595
        · exact R108599
        · exact R108603
        · exact R108607
        · exact R108611
        · exact R108615
        · exact R108619
        · exact R108623
        · exact R108627
        · exact R108631
        · exact R108635
        · exact R108639
        · exact R108643
        · exact R108647
        · exact R108651
        · exact R108655
        · exact R108659
        · exact R108663
        · exact R108667
        · exact R108671
        · exact R108675
        · exact R108679
        · exact R108683
        · exact R108687
        · exact R108691
        · exact R108695
        · exact R108699
        · exact R108703
        · exact R108707
        · exact R108711
        · exact R108715
        · exact R108719
        · exact R108723
        · exact R108727
        · exact R108731
        · exact R108735
        · exact R108739
        · exact R108743
        · exact R108747
        · exact R108751
        · exact R108755
        · exact R108759
        · exact R108763
        · exact R108767
        · exact R108771
        · exact R108775
        · exact R108779
        · exact R108783
        · exact R108787
        · exact R108791
        · exact R108795
        · exact R108799
        · exact R108803
        · exact R108807
        · exact R108811
        · exact R108815
        · exact R108819
        · exact R108823
        · exact R108827
        · exact R108831
        · exact R108835
        · exact R108839
        · exact R108843
        · exact R108847
        · exact R108851
        · exact R108855
        · exact R108859
        · exact R108863
        · exact R108867
        · exact R108871
        · exact R108875
        · exact R108879
        · exact R108883
        · exact R108887
        · exact R108891
        · exact R108895
        · exact R108899
        · exact R108903
        · exact R108907
        · exact R108911
        · exact R108915
        · exact R108919
        · exact R108923
        · exact R108927
        · exact R108931
        · exact R108935
        · exact R108939
        · exact R108943
        · exact R108947
        · exact R108951
        · exact R108955
        · exact R108959
        · exact R108963
        · exact R108967
        · exact R108971
        · exact R108975
        · exact R108979
        · exact R108983
        · exact R108987
        · exact R108991
        · exact R108995
        · exact R108999
        · exact R109003
        · exact R109007
        · exact R109011
        · exact R109015
        · exact R109019
        · exact R109023
        · exact R109027
        · exact R109031
        · exact R109035
        · exact R109039
        · exact R109043
        · exact R109047
        · exact R109051
        · exact R109055
        · exact R109059
        · exact R109063
        · exact R109067
        · exact R109071
        · exact R109075
        · exact R109079
        · exact R109083
        · exact R109087
        · exact R109091
        · exact R109095
        · exact R109099
        · exact R109103
        · exact R109107
        · exact R109111
        · exact R109115
        · exact R109119
        · exact R109123
        · exact R109127
        · exact R109131
        · exact R109135
        · exact R109139
        · exact R109143
        · exact R109147
        · exact R109151
        · exact R109155
        · exact R109159
        · exact R109163
        · exact R109167
        · exact R109171
        · exact R109175
        · exact R109179
        · exact R109183
        · exact R109187
        · exact R109191
        · exact R109195
        · exact R109199
        · exact R109203
        · exact R109207
        · exact R109211
        · exact R109215
        · exact R109219
        · exact R109223
        · exact R109227
        · exact R109231
        · exact R109235
        · exact R109239
        · exact R109243
        · exact R109247
        · exact R109251
        · exact R109255
        · exact R109259
        · exact R109263
        · exact R109267
        · exact R109271
        · exact R109275
        · exact R109279
        · exact R109283
        · exact R109287
        · exact R109291
        · exact R109295
        · exact R109299
        · exact R109303
        · exact R109307
        · exact R109311
        · exact R109315
        · exact R109319
        · exact R109323
        · exact R109327
        · exact R109331
        · exact R109335
        · exact R109339
        · exact R109343
        · exact R109347
        · exact R109351
        · exact R109355
        · exact R109359
        · exact R109363
        · exact R109367
        · exact R109371
        · exact R109375
        · exact R109379
        · exact R109383
        · exact R109387
        · exact R109391
        · exact R109395
        · exact R109399
        · exact R109403
        · exact R109407
        · exact R109411
        · exact R109415
        · exact R109419
        · exact R109423
        · exact R109427
        · exact R109431
        · exact R109435
        · exact R109439
        · exact R109443
        · exact R109447
        · exact R109451
        · exact R109455
        · exact R109459
        · exact R109463
        · exact R109467
        · exact R109471
        · exact R109475
        · exact R109479
        · exact R109483
        · exact R109487
        · exact R109491
        · exact R109495
        · exact R109499
        · exact R109503
        · exact R109507
        · exact R109511
        · exact R109515
        · exact R109519
        · exact R109523
        · exact R109527
        · exact R109531
        · exact R109535
        · exact R109539
        · exact R109543
        · exact R109547
        · exact R109551
        · exact R109555
        · exact R109559
        · exact R109563
        · exact R109567
        · exact R109571
        · exact R109575
        · exact R109579
        · exact R109583
        · exact R109587
        · exact R109591
        · exact R109595
        · exact R109599
        · exact R109603
        · exact R109607
        · exact R109611
        · exact R109615
        · exact R109619
        · exact R109623
        · exact R109627
        · exact R109631
        · exact R109635
        · exact R109639
        · exact R109643
        · exact R109647
        · exact R109651
        · exact R109655
        · exact R109659
        · exact R109663
        · exact R109667
        · exact R109671
        · exact R109675
        · exact R109679
        · exact R109683
        · exact R109687
        · exact R109691
        · exact R109695
        · exact R109699
        · exact R109703
        · exact R109707
        · exact R109711
        · exact R109715
        · exact R109719
        · exact R109723
        · exact R109727
        · exact R109731
        · exact R109735
        · exact R109739
        · exact R109743
        · exact R109747
        · exact R109751
        · exact R109755
        · exact R109759
        · exact R109763
        · exact R109767
        · exact R109771
        · exact R109775
        · exact R109779

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 109780) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 :=
  key m hm hodd (by omega)
