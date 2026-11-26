-- Prove2me | Theorems.Thm_Erdos287_dense_endpoint_carry_core
-- name    : Erdos287.dense_endpoint_carry_core
-- status  : Open
-- author  : @immiq
-- created : 2026-11-26T11:10:02.014914+00:00
-- url     : https://prove2.me/theorems/944d3e85-6ea8-5082-a185-5223247c0f09
-- title:
--   Dense endpoint-ratio branch with the lower prime-power constraints
-- statement:
--   Exclude any no-gap counterexample with $250M\le739m$ and $M>381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435$. The dense branch retains its unit-gap and run-count bounds. At exceptional maxima of the form $6\cdot3^j$ or $15\cdot5^j$, it also has the proved next-layer cofactor constraints. At the three-powered form, the neighbors of $5\cdot3^j$ are selected and neither can be twice a prime power.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.dense_endpoint_carry_core (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (hlarge : 381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435 < f (k - 1))
    (hratio : 250 * f (k - 1) ≤ 739 * f 0)
    (hunit : f (k - 1) < 2 * ((Finset.range (k - 1)).filter
      (fun i => f (i + 1) - f i = 1)).card)
    (hruns :
      let D := (Finset.range k).image f
      let R := (Finset.Icc (f 0) (f (k - 1) + 1 - 8)).filter
        (fun x => ∀ i ∈ Finset.range 8, x + i ∈ D)
      f (k - 1) < 100 * R.card)
    (hcarry : ∀ j : ℕ, 1 ≤ j →
      let D := (Finset.range k).image f
      (f (k - 1) = 6 * 3 ^ j → 4 * 3 ^ j ∈ D ∧ 5 * 3 ^ j ∉ D) ∧
      (f (k - 1) = 15 * 5 ^ j →
        let T := (Finset.Icc 6 14).filter (fun c => c ≠ 10 ∧ c * 5 ^ j ∉ D)
        (∑ c ∈ T, 72072 / c) % 5 = 2 ∧ (∀ c, T = {c} → c = 6 ∨ c = 11)))
    (hneighbors : ∀ j : ℕ, 1 ≤ j → f (k - 1) = 6 * 3 ^ j →
      let D := (Finset.range k).image f
      let r := 3 ^ j
      (5 * r - 1) ∈ D ∧ (5 * r + 1) ∈ D ∧
        ∀ p a : ℕ, p.Prime → 1 ≤ a →
          2 * p ^ a ≠ 5 * r - 1 ∧ 2 * p ^ a ≠ 5 * r + 1) : False := by sorry
