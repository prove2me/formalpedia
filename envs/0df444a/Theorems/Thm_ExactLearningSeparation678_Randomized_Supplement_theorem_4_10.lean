-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_Supplement_theorem_4_10
-- name    : ExactLearningSeparation678.Randomized.Supplement.theorem_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:29:41.521313+00:00
-- url     : https://prove2.me/theorems/3858da73-12d6-4a04-a9b0-370c1448dfdc
-- title:
--   Theorem 4.10 — comparison of $\gamma$, $f\gamma$, $\mathrm{ETD}$ and $\mathrm{fETD}$
-- statement:
--   For every concept class $C\subseteq\{0,1\}^N$,
--   $$\frac1{\gamma(C)}\le\frac1{f\gamma(C)},\qquad \mathrm{fETD}(C)\le\mathrm{ETD}(C),\qquad \mathrm{fETD}(C)\le\frac1{f\gamma(C)}\le2\,\mathrm{fETD}(C).$$
--
--   It summarizes Propositions 4.6 and 4.8 and Lemma 4.9: passing to fractional relaxations, the splitting parameter and the extended teaching dimension become the same quantity up to the factor $2$.
--
--   **Formalization Note** No cardinality hypothesis is added. Division is real division; for $|C|\le1$, $\gamma$, $f\gamma$ and $\mathrm{fETD}$ are $0$ ($\gamma$ and $f\gamma$ use the disclosed empty-infimum reading; $\mathrm{fETD}$ needs it only for the empty class), so every clause holds with both sides $0$ and the clauses for $|C|\ge2$ are the source's.
--
--   Differences from the source:
--   - encoding: coordinates [N] of C ⊆ {0,1}^N → an arbitrary finite type ι : Type with decidable equality, concepts ι → Bool; reason: a relabeling of [N]; every N, including N = 0, is an instance
--   - encoding: fγ(C) is the minimum over all real distributions on C with each atom at most 1/2 → real masses on the members of C, with fGamma the infimum of the finite-coordinate splitting objective over the capped probability simplex; reason: for |C| ≥ 2 the simplex is nonempty and compact and the objective is continuous, so its infimum is an attained minimum
--   - encoding: fETD(C,h) minimizes over c* ∈ C and all real nonnegative coordinate weights, then fETD(C) maximizes over every ambient h → fetdAt is the real infimum of the same total-weight objective over feasible pairs (c*, w); fetd is the supremum over all ambient Boolean functions; reason: for C nonempty feasible weights exist and can be clipped to [0,1] without violating any constraint or increasing cost; finitely many c* and compact weight cubes give attainment, and the outer index is finite and nonempty
--   - reading: γ and fγ have no feasible optimization point when |C| ≤ 1; fETD has none only when C is empty; the source assigns no value in these cases → empty real infima are 0 and real division by 0 is 0; fETD of a singleton is already 0 using feasible zero weights; reason: this supplies values only for undefined degenerate extrema; every trivial-class clause is true and every source-defined nontrivial instance is retained
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Theorem 4.10, p.33; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Supplement_Teaching

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized.Supplement

open QAlgorithms.Learning

/-- Theorem 4.10, p.33: for every concept class, `1/γ(C) ≤ 1/fγ(C)`, `fETD(C) ≤ ETD(C)`, and
`fETD(C) ≤ 1/fγ(C) ≤ 2 fETD(C)` (no cardinality hypothesis; real division, with the zero reading
of `γ`, `fγ`, `fETD` at `|C| ≤ 1`). -/
theorem theorem_4_10 (ι : Type) [Fintype ι] [DecidableEq ι] (C : Finset (ι → Bool)) :
    1 / gammaParam C ≤ 1 / fGamma C ∧ fetd C ≤ (etd C : ℝ) ∧
    fetd C ≤ 1 / fGamma C ∧ 1 / fGamma C ≤ 2 * fetd C := by sorry

end ExactLearningSeparation678.Randomized.Supplement
