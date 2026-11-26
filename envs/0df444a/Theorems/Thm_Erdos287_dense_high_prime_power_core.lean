-- Prove2me | Theorems.Thm_Erdos287_dense_high_prime_power_core
-- name    : Erdos287.dense_high_prime_power_core
-- status  : Open
-- author  : @immiq
-- created : 2026-11-26T11:26:50.957802+00:00
-- url     : https://prove2.me/theorems/4ac783d4-14ba-5258-b46f-15e040035059
-- title:
--   Dense Erdős 287 branch with uniform high prime-power limitations
-- statement:
--   Exclude an Erdős #287 counterexample above the Main3 finite endpoint in the dense ratio branch with the certified count and exceptional endpoint properties. In addition, a nonempty prime-power layer $q=p^e$ satisfying $M-m<3q$ obeys one of the five proved patterns for $p\in\{3,5,7,13\}$. Each dyadic layer $q=2^e>M/10$ is empty or a pair of distinct multiples with cofactors from $\{3,5,7,9\}$ other than the pair $\{3,9\}$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.dense_high_prime_power_core (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
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
          2 * p ^ a ≠ 5 * r - 1 ∧ 2 * p ^ a ≠ 5 * r + 1)
    (hlargeprime : ∀ p e : ℕ, p.Prime → 1 ≤ e → f (k - 1) < f 0 + 3 * p ^ e →
      let q := p ^ e
      let H := ((Finset.range k).image f).filter (fun n => q ∣ n)
      H = ∅ ∨
        (p = 3 ∧ H = {q, 2 * q}) ∨
        (p = 5 ∧ H = {2 * q, 3 * q}) ∨
        (p = 7 ∧ H = {3 * q, 4 * q}) ∨
        (p = 3 ∧ H = {2 * q, 4 * q}) ∨
        (p = 13 ∧ H = {2 * q, 3 * q, 4 * q}))
    (hdyadic : ∀ e : ℕ, 1 ≤ e → f (k - 1) < 10 * 2 ^ e →
      let q := 2 ^ e
      let H := ((Finset.range k).image f).filter (fun n => q ∣ n)
      H = ∅ ∨ ∃ a ∈ ({3, 5, 7, 9} : Finset ℕ), ∃ b ∈ ({3, 5, 7, 9} : Finset ℕ),
        a < b ∧ (a ≠ 3 ∨ b ≠ 9) ∧ H = {a * q, b * q}) : False := by sorry
