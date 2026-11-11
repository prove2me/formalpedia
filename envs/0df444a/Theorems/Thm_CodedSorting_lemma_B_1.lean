-- Prove2me | Theorems.Thm_CodedSorting_lemma_B_1
-- name    : CodedSorting.lemma_B_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T23:05:04.730703+00:00
-- url     : https://prove2.me/theorems/ec84c58c-e187-4119-8fd6-f666edeca0b6
-- title:
--   Lemma B.1 — $\varepsilon\ln 512<33/338432$ for $\varepsilon=3/200000$
-- statement:
--   For $m=512$, $\varepsilon=3/200000=1.5\times10^{-5}$ and $\eta=33/338432$,
--   $$\varepsilon\ln m<\eta .$$
--
--   Together with $1-x<e^{-x}$ this gives $S/W=m(1-\eta)<m^{1-\varepsilon}$ in Corollary 5.4, which fixes the exponent of the sorting bound.
--
--   Differences from the source: none.
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), Lemma B.1, p.36 (PDF 37)

import Mathlib

namespace CodedSorting

/-- **Lemma B.1 (Parameter inequality)**, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), p.36.

For `m = 512`, `ε = 3/200000 = 1.5 × 10⁻⁵` and `η = 33/338432`, `ε ln m < η`.

**Formalization Note.** `Real.log` is the natural logarithm `ln`. -/
theorem lemma_B_1 : (3 : ℝ) / 200000 * Real.log 512 < 33 / 338432 := by sorry

end CodedSorting
