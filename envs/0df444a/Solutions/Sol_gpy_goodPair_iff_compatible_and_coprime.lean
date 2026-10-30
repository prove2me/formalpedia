-- Prove2me | solution 1 for gpy_goodPair_iff_compatible_and_coprime
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T01:10:34.396993+00:00
-- url     : https://prove2.me/submissions/cefb3d20-b35c-4675-816c-fb26cd5f68ad

/- Submission file for the Prove2Me problem `gpy_goodPair_iff_compatible_and_coprime` (publish2 first-moment batch).
   Self-contained: imports Mathlib only. Top-level `theorem solution` in the
   problem's exact binder/statement form (statement mechanically extracted
   from the restated theorem, so the two are textually identical modulo
   the theorem name). No sorry tactic, no axioms beyond the standard
   ones, no platform imports. -/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false

theorem solution {k : ℕ} {h d e : Fin k → ℕ}
    {i : Fin k} :
    (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ↔
    (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
      ∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
        Nat.Coprime (w + h i)
          (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) := by
  have hcompat : ∀ (d e : Fin k → ℕ) (i : Fin k),
      (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
        Nat.Coprime (w + h i)
          (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) →
      ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
        h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))] := by
    intro d e i hg
    obtain ⟨w, hw, -⟩ := hg
    intro i' _ j' _
    have h1 : w + h i' ≡ 0
        [MOD Nat.gcd (Nat.lcm (d i') (e i')) (Nat.lcm (d j') (e j'))] :=
      Nat.modEq_zero_iff_dvd.mpr
        (dvd_trans (Nat.gcd_dvd_left _ _) (hw i'))
    have h2 : w + h j' ≡ 0
        [MOD Nat.gcd (Nat.lcm (d i') (e i')) (Nat.lcm (d j') (e j'))] :=
      Nat.modEq_zero_iff_dvd.mpr
        (dvd_trans (Nat.gcd_dvd_right _ _) (hw j'))
    exact Nat.ModEq.add_left_cancel' w (h1.trans h2.symm)
  constructor
  · intro hg
    exact ⟨hcompat d e i hg, hg⟩
  · rintro ⟨-, w, hw, hcop⟩
    exact ⟨w, hw, hcop⟩
