-- Prove2me | Theorems.Thm_Erdos287_upper_sieve_type_I_II_levels_below_seven_thirteenths
-- name    : Erdos287.upper_sieve_type_I_II_levels_below_seven_thirteenths
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T18:05:28.538+00:00
-- url     : https://prove2.me/theorems/28d3930c-869c-5f14-9929-f287820ab965
-- title:
--   Upper sieve exponent margins up to level 7/13 in Erdős 287
-- statement:
--   For every main level $\theta$ in $[269/500,7/13)$, set $t=(5\theta+1)/12$. The four-fold Heath–Brown exponents have a smooth Type I variable at least $t$ or a single Type II variable in $[0.12,t]$. The Type I and Type II inequalities hold with the prescribed positive slack. The example level $673/1250$ has upper sieve coefficient $2500/673<3.715$ and fits the period $(u,v)=(39,106)$.
-- source:
--   Erdős #287, upper linear sieve with mixed residue conditions.

import Mathlib

theorem Erdos287.upper_sieve_type_I_II_levels_below_seven_thirteenths {ι : Type*} [DecidableEq ι] (I smooth : Finset ι) (x : ι → ℝ)
    (hcard : I.card ≤ 8) (hsum : ∑ i ∈ I, x i = 1)
    (hrough : ∀ i ∈ I, i ∉ smooth → x i ≤ 251 / 1000)
    (θ ε : ℝ) (hθlo : 269 / 500 ≤ θ) (_hθhi : θ < 7 / 13)
    (hε : 0 < ε) (hεmax : ε ≤ (7 - 13 * θ) / 1000) :
    let t := (5 * θ + 1) / 12
    ((∃ i ∈ I, i ∈ smooth ∧ t ≤ x i) ∨
      ∃ i ∈ I, 3 / 25 ≤ x i ∧ x i ≤ t) ∧
    (∀ m r s : ℝ, t ≤ m → m ≤ 1 → 0 ≤ r → 0 ≤ s →
      s ≤ m - ε → r ≤ θ - m + 2 * ε →
      (s - m) / 2 ≤ -ε / 2 ∧
      r + s / 2 + 1 / 2 ≤ 1 - ε ∧
      r + s / 4 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      3 * r / 4 + s / 2 + (1 - m) / 4 + 1 / 2 ≤ 1 - ε ∧
      r / 2 + s / 4 - 3 * m / 4 ≤ -ε) ∧
    (∀ ν r s : ℝ, 3 / 25 ≤ ν → ν ≤ t → 0 ≤ r → 0 ≤ s →
      r + s ≥ 1 / 2 - ε → r ≤ θ - ν + 2 * ε → s ≤ ν - ε →
      r - s / 2 + ν ≤ 1 / 2 - ε ∧
      2 * r + ν ≤ 1 - ε ∧
      r / 2 + 5 * ν / 4 ≤ 1 / 2 - ε ∧
      3 * r / 4 + ν ≤ 1 / 2 - ε ∧
      r + 3 * ν / 2 ≤ 1 - ε) ∧
    269 / (500 : ℝ) ≤ 673 / 1250 ∧ 673 / (1250 : ℝ) < 7 / 13 ∧
    2 / (673 / 1250 : ℝ) < 743 / 200 ∧ 2 / (673 / 1250 : ℝ) < 145 / 39 ∧
    106 / (39 : ℝ) < Real.exp 1 := by sorry
