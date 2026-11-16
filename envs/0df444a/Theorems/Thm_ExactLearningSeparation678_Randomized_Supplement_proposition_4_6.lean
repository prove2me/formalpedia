-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_Supplement_proposition_4_6
-- name    : ExactLearningSeparation678.Randomized.Supplement.proposition_4_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T20:28:07.7093+00:00
-- url     : https://prove2.me/theorems/bf3be4ce-e00e-44f7-8e9d-742184d43240
-- title:
--   Proposition 4.6 — $1/\gamma(C)\le1/f\gamma(C)$
-- statement:
--   For every concept class $C\subseteq\{0,1\}^N$,
--   $$\frac1{\gamma(C)}\le\frac1{f\gamma(C)},$$
--   where $\gamma(C)=\min_{S\subseteq C,|S|\ge2}\max_i\min\{|S_{i,0}|,|S_{i,1}|\}/|S|$ is the splitting parameter and $f\gamma(C)$ is the fractional splitting parameter of Definition 4.5.
--
--   The fractional relaxation can only make the reciprocal splitting parameter larger; this is the first clause of Theorem 4.10.
--
--   **Formalization Note** Division is real division; for $|C|\le1$ both $\gamma(C)$ and $f\gamma(C)$ are read as $0$ and both sides are $0$.
--
--   Differences from the source:
--   - encoding: coordinates [N] of C ⊆ {0,1}^N → an arbitrary finite type ι : Type with decidable equality, concepts ι → Bool; reason: a relabeling of [N]; every N, including N = 0, is an instance
--   - encoding: fγ(C) is the minimum over all real distributions on C with each atom at most 1/2 → real masses on the members of C, with fGamma the infimum of the finite-coordinate splitting objective over the capped probability simplex; reason: for |C| ≥ 2 the simplex is nonempty and compact and the objective is continuous, so its infimum is an attained minimum
--   - reading: γ and fγ have no feasible optimization point when |C| ≤ 1; fETD has none only when C is empty; the source assigns no value in these cases → empty real infima are 0 and real division by 0 is 0; fETD of a singleton is already 0 using feasible zero weights; reason: this supplies values only for undefined degenerate extrema; every trivial-class clause is true and every source-defined nontrivial instance is retained
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Proposition 4.6, p.31; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Supplement_Teaching

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized.Supplement

open QAlgorithms.Learning

/-- Proposition 4.6, p.31: `1/γ(C) ≤ 1/fγ(C)` for every concept class (real division; both sides
are `0` when `|C| ≤ 1`). -/
theorem proposition_4_6 (ι : Type) [Fintype ι] [DecidableEq ι] (C : Finset (ι → Bool)) :
    1 / gammaParam C ≤ 1 / fGamma C := by sorry

end ExactLearningSeparation678.Randomized.Supplement
