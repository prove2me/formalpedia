-- Prove2me | Theorems.Thm_Erdos287_matched_outer_rows_cauchy_schwarz
-- name    : Erdos287.matched_outer_rows_cauchy_schwarz
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T18:51:24.193412+00:00
-- url     : https://prove2.me/theorems/a7eaf0b2-ade1-5098-ab97-7832ec1a124b
-- title:
--   Cauchy–Schwarz with a matched class in every dispersion row
-- statement:
--   Each row $i$ has positive base modulus $b_i$ and a prescribed class modulo $b_i$. Fix a lift factor $T$. Sum a real array over the rows and those $u\in[0,b_iT)$ in the prescribed class for their row. The squared sum is at most the number of rows times $T$ times the sum of squares over every row and every $u\in[0,b_iT)$.
-- source:
--   Erdős #287, retaining the matched residue class in the Type II outer count.

import Mathlib

theorem Erdos287.matched_outer_rows_cauchy_schwarz {ι : Type*} (rows : Finset ι) (modulus residue : ι → ℕ) (T : ℕ)
    (hmodulus : ∀ i ∈ rows, 0 < modulus i) (value : ι → ℕ → ℝ) :
    let matched (i : ι) := (Finset.range (modulus i * T)).filter (fun u => u ≡ residue i [MOD modulus i])
    (∑ i ∈ rows, ∑ u ∈ matched i, value i u) ^ 2 ≤
      (rows.card : ℝ) * T * (∑ i ∈ rows, ∑ u ∈ Finset.range (modulus i * T), value i u ^ 2) := by sorry
