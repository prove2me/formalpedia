-- Prove2me | Theorems.Thm_Erdos287_gap_from_simultaneous_valuation_scan
-- name    : Erdos287.gap_from_simultaneous_valuation_scan
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T05:35:48.069862+00:00
-- url     : https://prove2.me/theorems/f1c8e798-16d6-5ca1-901b-4b5a78977c49
-- title:
--   Simultaneous prime-power residue certificates for the denominator gap
-- statement:
--   For a unit-fraction representation of 1, scan any duplicate-free list covering the denominators that matter to the chosen prime-power congruences. If neither possible status of its first entry has the zero vector among the reachable residue states, some consecutive gap is at least three.
-- source:
--   Erdős Problem #287. Joint verification of the upper-valuation congruences with the condition on consecutive omissions.

import Mathlib

theorem Erdos287.gap_from_simultaneous_valuation_scan (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
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
    (hcert :
      let G := (j : Fin r) → ZMod (p j ^ (a j + 1 - b j))
      let w : ℕ → G := fun n j =>
        if b j ≤ padicValNat (p j) n then
          (((L j / (n / p j ^ padicValNat (p j) n)) *
            p j ^ (a j - padicValNat (p j) n) : ℕ) : ZMod (p j ^ (a j + 1 - b j)))
        else 0
      let s := xs.foldr (fun n (q : Option ℕ × Finset G × Finset G) =>
        (some n,
          if n ∈ holes then ∅ else (q.2.1 ∪ q.2.2).image (fun u => w n + u),
          if n = f 0 ∨ n = f (k - 1) then ∅ else
            if q.1 = some (n + 1) then q.2.1 else q.2.1 ∪ q.2.2))
        (none, {0}, {0})
      0 ∉ s.2.1 ∪ s.2.2) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
