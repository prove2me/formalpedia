-- Prove2me | Theorems.Thm_DynSort_lemma_5
-- name    : DynSort.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:33:48.594362+00:00
-- url     : https://prove2.me/theorems/0415c4d1-f228-45e4-bc34-f0f78713a597
-- title:
--   Lemma 5 — crossings of a subsequence; $\mathrm{cost}(S')\le C\cdot\mathrm{OPT}(S')$
-- statement:
--   Let $S'$ be a subsequence of a finite sequence $S$ of reals. Then for every threshold $z$,
--   $$\mathrm{cross}_z(S')\le\mathrm{cross}_z(S),$$
--   and, for every real $C$, if $\mathrm{cross}_z(S)\le C$ for every $z$, then
--   $$\mathrm{cost}(S')\le C\cdot\mathrm{OPT}(S').$$
--
--   This is how the crossing bound of the full A-DST, virtual elements included, transfers to the active elements, and why the reduction to deletion–insertion pairs preserves the competitive ratio.
--
--   Differences from the source: none.
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Lemma 5, p.7 (PDF p.9); proof p.44 (PDF p.46)

import Mathlib
import Definitions.Def_DynSort_cost
import Definitions.Def_DynSort_cross

namespace DynSort

/-- **Lemma 5**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §2, p.7 (PDF p.9; proof p.44): "Let S′ be a subsequence of a sequence S.
Then, for every threshold z, cross_z(S′) ≤ cross_z(S). In particular, if cross_z(S) ≤ C for every
z, then cost(S′) ≤ C · OPT(S′)."

**Formalization Note.** A subsequence is `List.Sublist`; `C` is any real. -/
theorem lemma_5 (S S' : List ℝ) (h : S'.Sublist S) :
    (∀ z : ℝ, cross z S' ≤ cross z S) ∧
      ∀ C : ℝ, (∀ z : ℝ, (cross z S : ℝ) ≤ C) → cost S' ≤ C * opt S' := by sorry

end DynSort
