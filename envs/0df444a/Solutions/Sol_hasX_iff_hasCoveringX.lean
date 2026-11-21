-- Prove2me | solution 1 for hasX_iff_hasCoveringX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T15:07:27.117256+00:00
-- url     : https://prove2.me/submissions/75df7e9d-6c78-4787-b523-1b21ed25dffd

import Mathlib
import Definitions.Def_Basic

set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]
theorem _root_.solution [Finite P] :
    (∃ a b c d m : P, IsX a b c d m) ↔
    (∃ a b c d m : P, IsCoveringX a b c d m) := by
  constructor
  · intro ⟨a, b, c, d, m, h1, h2, h3, h4, h5, h6⟩
    haveI : Fintype P := Fintype.ofFinite P
    haveI : DecidableRel (α := P) (· < ·) := fun _ _ => Classical.dec _
    haveI : DecidableRel (α := P) (· ≤ ·) := fun _ _ => Classical.dec _
    -- Step 1: pick a maximal element m' of M = {x | m ≤ x ∧ x < c ∧ x < d}
    let M : Finset P := Finset.univ.filter (fun x => m ≤ x ∧ x < c ∧ x < d)
    have hMne : M.Nonempty :=
      ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl _, h2, h4⟩⟩
    obtain ⟨m', hm'M, hm'max⟩ := M.exists_maximal hMne
    rw [Finset.mem_filter] at hm'M
    obtain ⟨-, hm'm, hm'c, hm'd⟩ := hm'M
    -- Step 2: pick a minimal element c' of A = {x | m' < x ∧ x ≤ c}
    let A : Finset P := Finset.univ.filter (fun x => m' < x ∧ x ≤ c)
    have hAne : A.Nonempty :=
      ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm'c, le_refl _⟩⟩
    obtain ⟨c', hc'A, hc'min⟩ := A.exists_minimal hAne
    rw [Finset.mem_filter] at hc'A
    obtain ⟨-, hm'c', hc'c⟩ := hc'A
    -- Step 3: m' ⋖ c'
    have hcov : m' ⋖ c' :=
      ⟨hm'c', fun z hm'z hzc' => by
        have hzA : z ∈ A := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hm'z, (hzc'.trans_le hc'c).le⟩
        exact lt_irrefl c' (lt_of_le_of_lt (hc'min hzA hzc'.le) hzc')⟩
    -- Step 4: c' ⊥ d
    -- For ¬ c' ≤ d: if c' < c then c' ∈ M contradicts maximality of m';
    --               if c' = c then c ≤ d contradicts h6
    -- For ¬ d ≤ c': d < c' contradicts m' ⋖ c'; d = c' gives d ≤ c contradicting h6
    have hc'd : c' ⊥ d := by
      refine ⟨fun hle => ?_, fun hle => ?_⟩
      · rcases hc'c.lt_or_eq with hc'c_lt | hc'c_eq
        · rcases hle.lt_or_eq with hc'd_lt | hc'd_eq
          · -- c' < c and c' < d: c' ∈ M, contradicts maximality of m'
            have hc'M : c' ∈ M := Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, hm'm.trans hm'c'.le, hc'c_lt, hc'd_lt⟩
            exact lt_irrefl m' (lt_of_lt_of_le hm'c' (hm'max hc'M hm'c'.le))
          · -- c' = d, so d < c, contradicts c ⊥ d
            exact h6.2 (hc'd_eq.symm.le.trans hc'c_lt.le)
        · -- c' = c, so c ≤ d, contradicts c ⊥ d
          exact h6.1 (hc'c_eq.symm.le.trans hle)
      · rcases hle.lt_or_eq with hlt | heq
        · exact hcov.2 hm'd hlt
        · exact h6.2 (heq.le.trans hc'c)
    -- Conclude
    exact ⟨a, b, c', d, m',
      h1.trans_le hm'm, hcov, h3.trans_le hm'm, hm'd, h5, hc'd⟩
  · rintro ⟨a, b, c, d, m, h1, h2, h3, h4, h5, h6⟩
    exact ⟨a, b, c, d, m, h1, h2.lt, h3, h4, h5, h6⟩
