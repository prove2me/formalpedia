-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_Supplement_lemma_4_9
-- name    : ExactLearningSeparation678.Randomized.Supplement.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:29:15.622327+00:00
-- url     : https://prove2.me/theorems/832a1d63-e22f-4237-b0fc-407d83ad2d49
-- title:
--   Lemma 4.9 — $\mathrm{fETD}(C)\le1/f\gamma(C)\le2\,\mathrm{fETD}(C)$
-- statement:
--   For every concept class $C\subseteq\{0,1\}^N$ with $|C|\ge2$,
--   $$\mathrm{fETD}(C)\le\frac1{f\gamma(C)}\le2\,\mathrm{fETD}(C).$$
--
--   The two fractional relaxations, of the splitting parameter and of the extended teaching dimension, thus agree up to a factor of two. This is the third clause of Theorem 4.10, and it converts the bounds of Theorems 4.11 and 4.12 into each other in Theorem 1.6.
--
--   Differences from the source:
--   - encoding: coordinates [N] of C ⊆ {0,1}^N → an arbitrary finite type ι : Type with decidable equality, concepts ι → Bool; reason: a relabeling of [N]; every N, including N = 0, is an instance
--   - encoding: fγ(C) is the minimum over all real distributions on C with each atom at most 1/2 → real masses on the members of C, with fGamma the infimum of the finite-coordinate splitting objective over the capped probability simplex; reason: for |C| ≥ 2 the simplex is nonempty and compact and the objective is continuous, so its infimum is an attained minimum
--   - encoding: fETD(C,h) minimizes over c* ∈ C and all real nonnegative coordinate weights, then fETD(C) maximizes over every ambient h → fetdAt is the real infimum of the same total-weight objective over feasible pairs (c*, w); fetd is the supremum over all ambient Boolean functions; reason: for C nonempty feasible weights exist and can be clipped to [0,1] without violating any constraint or increasing cost; finitely many c* and compact weight cubes give attainment, and the outer index is finite and nonempty
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Lemma 4.9, p.32 (proof pp.32–33); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Supplement_Teaching

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized.Supplement

open QAlgorithms.Learning

/-- Lemma 4.9, p.32: for every concept class with `|C| ≥ 2`,
`fETD(C) ≤ 1/fγ(C) ≤ 2 fETD(C)`. -/
theorem lemma_4_9 (ι : Type) [Fintype ι] [DecidableEq ι] (C : Finset (ι → Bool))
    (hC : 2 ≤ C.card) :
    fetd C ≤ 1 / fGamma C ∧ 1 / fGamma C ≤ 2 * fetd C := by sorry

end ExactLearningSeparation678.Randomized.Supplement
