-- Prove2me | Theorems.Thm_Erdos287_gap_from_residues_and_omission_mass
-- name    : Erdos287.gap_from_residues_and_omission_mass
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T05:44:09.113733+00:00
-- url     : https://prove2.me/theorems/06048221-89bb-49b6-bd3d-d84d24d99631
-- title:
--   Prime-power residue certificates with an omission-mass bound
-- statement:
--   For a unit-fraction representation of 1, bound the scaled reciprocal mass of omitted integers by the total reciprocal sum of the interval minus one. A sparse scan rules out a gap-free list whenever every reachable zero-residue choice omits more than this bound.
-- source:
--   Erdős Problem #287. A joint prime-power residue certificate augmented with a rigorous reciprocal-mass budget.

import Mathlib

theorem Erdos287.gap_from_residues_and_omission_mass (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (r : ℕ) (p b a L : Fin r → ℕ)
    (hp : ∀ j, (p j).Prime) (hb : ∀ j, 1 ≤ b j) (hba : ∀ j, b j ≤ a j)
    (xs : List ℕ) (hxs : xs.Nodup)
    (hspan : ∀ n ∈ xs, f 0 ≤ n ∧ n ≤ f (k - 1))
    (hcover : ∀ j i, i < k → b j ≤ padicValNat (p j) (f i) → f i ∈ xs)
    (hcoeff : ∀ j i, i < k → b j ≤ padicValNat (p j) (f i) →
      padicValNat (p j) (f i) ≤ a j ∧
        f i / p j ^ padicValNat (p j) (f i) ∣ L j)
    (holes : Finset ℕ) (hholes : ∀ i, i < k → f i ∉ holes)
    (cost : ℕ → ℕ) (scale budget : ℕ)
    (hcost : ∀ n ∈ xs, (cost n : ℚ) ≤ (scale : ℚ) / n)
    (hbudget : (scale : ℚ) *
      ((∑ n ∈ Finset.Icc (f 0) (f (k - 1)), (1 : ℚ) / n) - 1) ≤ (budget : ℚ))
    (hcert :
      let G := (j : Fin r) → ZMod (p j ^ (a j + 1 - b j))
      let w : ℕ → G := fun n j =>
        if b j ≤ padicValNat (p j) n then
          (((L j / (n / p j ^ padicValNat (p j) n)) *
            p j ^ (a j - padicValNat (p j) n) : ℕ) : ZMod (p j ^ (a j + 1 - b j)))
        else 0
      let s := xs.foldr (fun n (q : Option ℕ × Finset (G × ℕ) × Finset (G × ℕ)) =>
        (some n,
          if n ∈ holes then ∅ else (q.2.1 ∪ q.2.2).image (fun u => (w n, cost n) + u),
          if n = f 0 ∨ n = f (k - 1) then ∅ else
            if q.1 = some (n + 1) then q.2.1 else q.2.1 ∪ q.2.2))
        (none, {0}, {0})
      ∀ u ∈ s.2.1 ∪ s.2.2, u.1 = 0 →
        u.2 + budget < ∑ n ∈ xs.toFinset, cost n) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
