-- Prove2me | solution 1 for erdos_szekeres_conjecture
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:56:17.078409+00:00
-- url     : https://prove2.me/submissions/f1ee6166-2e99-41a4-ba51-3038c37d5d8b

import Mathlib

set_option autoImplicit false

theorem solution : ¬ (
    ∀ (k : ℕ), 3 ≤ k →
    ∃ (N : ℕ) (_ : N = 2 ^ (k - 2) + 1),
    ∀ (pts : Fin N → ℝ × ℝ),
      Function.Injective pts →
      (∀ i j m : Fin N, i ≠ j → j ≠ m → i ≠ m →
        ¬ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
          pts m = ((pts i).1 + t * ((pts j).1 - (pts i).1),
                   (pts i).2 + t * ((pts j).2 - (pts i).2))) →
      ∃ (S : Finset (Fin N)) (_ : S.card = k),
        ∀ i ∈ S, ∀ j ∈ S, ∀ m ∈ S,
          i ≠ j → j ≠ m → i ≠ m →
          ¬ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
            pts m = ((pts i).1 + t * ((pts j).1 - (pts i).1),
                     (pts i).2 + t * ((pts j).2 - (pts i).2)) → False) := by
  intro h
  obtain ⟨N, hN, hprop⟩ := h 3 (by omega)
  norm_num at hN
  subst N
  let pts : Fin 3 → ℝ × ℝ := ![(0, 0), (1, 0), (0, 1)]
  have hinj : Function.Injective pts := by
    clear h hprop
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [pts]
  have hgen : ∀ i j m : Fin 3, i ≠ j → j ≠ m → i ≠ m →
      ¬ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
        pts m = ((pts i).1 + t * ((pts j).1 - (pts i).1),
                 (pts i).2 + t * ((pts j).2 - (pts i).2)) := by
    clear h hprop hinj
    intro i j m hij hjm him ht
    obtain ⟨t, ht0, ht1, hp⟩ := ht
    fin_cases i <;> fin_cases j <;> fin_cases m <;> simp_all [pts] <;> linarith
  obtain ⟨S, hcard, hbad⟩ := hprop pts hinj hgen
  have hS : S = Finset.univ := S.eq_univ_of_card (by simpa using hcard)
  have hb := hbad 0 (by simp [hS]) 1 (by simp [hS]) 2 (by simp [hS])
    (by decide) (by decide) (by decide)
  apply hb
  refine ⟨0, ?_⟩
  intro ht
  exact (lt_irrefl (0 : ℝ)) ht.1

#print axioms solution
