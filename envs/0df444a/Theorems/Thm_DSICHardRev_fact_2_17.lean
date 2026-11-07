-- Prove2me | Theorems.Thm_DSICHardRev_fact_2_17
-- name    : DSICHardRev.fact_2_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:38.574787+00:00
-- url     : https://prove2.me/theorems/e9d7f472-4c8a-4990-a185-824bf21767ce
-- title:
--   Fact 2.17 — gross substitutes is preserved under convolution
-- statement:
--   Let $\iota$ be a finite set of items and let $f,g:2^{\iota}\to\mathbb R_{\ge0}$ be gross substitutes. Then their convolution
--   $$(f\star g)(S)=\max_{T\subseteq S}\{f(S\setminus T)+g(T)\}$$
--   is gross substitutes.
--
--   The GS hard valuations of Proposition 3.2 are convolutions of two weighted matroid rank functions; this fact is what makes them GS.
--
--   **Formalization Note** Gross substitutes is the Kelso–Crawford condition at all real price vectors.
--
--   Differences from the source:
--   - reading: GS valuations (not defined in the paper) → Kelso–Crawford gross substitutes at all real price vectors (published GrossSubstitutesOn v Set.univ); reason: the standard definition; requiring all real prices is the more restrictive class; the paper's sources (Fujishige–Yang, Murota) use it
--   - encoding: items M = [m] → an arbitrary finite item type ι; reason: the same statement up to relabelling the items
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §2.3, p.10, Fact 2.17 (with Definition 2.16)

import Mathlib
import Definitions.Def_KelsoCrawford_OneSided_Model
import Definitions.Def_DSICHardRev_ValuationClasses

namespace DSICHardRev

/-- **Fact 2.17** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §2.3, p.10):
gross substitutes is preserved under convolution (Definition 2.16).

**Formalization Note.** `f, g : 2^ι → ℝ₊` as in Definition 2.16 (non-negative), GS in the
Kelso–Crawford sense at all real price vectors (`GrossSubstitutesOn · Set.univ`); the convolution
is `conv f g S = max_{T ⊆ S} (f (S \ T) + g T)`. -/
theorem fact_2_17 {ι : Type} [Fintype ι] [DecidableEq ι] (f g : Finset ι → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hg0 : ∀ S, 0 ≤ g S)
    (hf : KelsoCrawford.OneSided.GrossSubstitutesOn f Set.univ)
    (hg : KelsoCrawford.OneSided.GrossSubstitutesOn g Set.univ) :
    KelsoCrawford.OneSided.GrossSubstitutesOn (conv f g) Set.univ := by sorry

end DSICHardRev
