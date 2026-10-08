-- Prove2me | Theorems.Thm_Erdos3_szemeredi_positive_upper_density
-- name    : Erdos3.szemeredi_positive_upper_density
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T17:18:50.50531+00:00
-- url     : https://prove2.me/theorems/f47e9f0c-25a2-44af-9fe2-47daf099e52c
-- title:
--   Szemerédi's theorem (positive upper density)
-- statement:
--   **Szemerédi's theorem.** If $A\subseteq\mathbb N$ has positive upper density,
--
--   $$\limsup_{N\to\infty}\frac{|A\cap\{0,\dots,N-1\}|}{N}>0,$$
--
--   then $A$ contains arithmetic progressions of every finite length. Conjectured by Erdős and Turán (1936), proved by Roth for $k=3$ (1953) and by Szemerédi in general (1975). A set of positive upper density has divergent reciprocal sum, so this is the density case of the goal.
-- source:
--   E. Szemerédi, *On sets of integers containing no k elements in arithmetic progression*, Acta Arith. 27 (1975), 199–245, main theorem; cited at https://www.erdosproblems.com/3

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos3
open Erdos142

theorem szemeredi_positive_upper_density (A : Set ℕ)
    (hA : ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ N : ℕ in Filter.atTop, δ * N ≤ ((A ∩ Set.Iio N).ncard : ℝ)) :
    ∀ k : ℕ, ∃ S ⊆ A, IsAPOfLength S k := by
  sorry

end Erdos3
