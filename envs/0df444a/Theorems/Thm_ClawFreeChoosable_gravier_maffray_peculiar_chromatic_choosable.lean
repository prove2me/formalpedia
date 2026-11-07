-- Prove2me | Theorems.Thm_ClawFreeChoosable_gravier_maffray_peculiar_chromatic_choosable
-- name    : ClawFreeChoosable.gravier_maffray_peculiar_chromatic_choosable
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:13.009113+00:00
-- url     : https://prove2.me/theorems/b056f92a-74fe-487d-970f-24f792391f06
-- title:
--   §13 ([GM98, Corollary 2]) — peculiar graphs are chromatic-choosable
-- statement:
--   Every finite peculiar graph $H$ (Definition 12.4, the cliques $K_1, K_2, K_3$ possibly empty) satisfies
--   $$\mathrm{ch}(H) = \chi(H).$$
--
--   This result of Gravier and Maffray ([GM98, Corollary 2, p.89]) is cited, not proved, in the paper; it settles the peculiar case of Theorem 1.3 when no colours are prescribed.
--
--   Differences from the source:
--   - reading: peculiar, in a result cited from [GM98], whose peculiar graphs have all nine cliques nonempty; the paper invokes it only when K1, K2, K3 are nonempty → IsPeculiar of Definition 12.4 (K1, K2, K3 may be empty); reason: the paper's own definition and the more general hypothesis; a degenerate peculiar graph is cobipartite (p.37), hence perfect and ω-choosable by Theorem 8.3 with C = ∅, so the statement is still true
--   - encoding: ch(H), χ(H) → OAI.LinearListHadwiger.listChromaticNumber H (cast to ℕ∞) and Mathlib's chromaticNumber H in ℕ∞; reason: Lean convention; finite graphs, same values
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, §13, p.37 (PDF p.40), first paragraph; cited from [GM98, Corollary 2, p.89]

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_ClawFreeChoosable_IsPeculiar

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Gravier–Maffray [GM98, Corollary 2, p.89]** (Mishra, Narayanan N, Shankar, *Claw-free perfect graphs are chromatic-choosable*, arXiv:2611.01068v1, §13, p.37, first paragraph): every
peculiar graph `H` satisfies `ch(H) = χ(H)`.

**Formalization Note.** Cited in the paper, not proved there (unnumbered; S. Gravier, F. Maffray, *Graphs
whose choice number is equal to their chromatic number*, J. Graph Theory 27 (1998) [GM98]). "Peculiar" is
Definition 12.4 as printed (`IsPeculiar`: the cliques `K₁, K₂, K₃` may be empty), the more general
hypothesis. `ch` is the published `listChromaticNumber`; `χ` is Mathlib's `chromaticNumber` in
`ℕ∞`. -/
theorem gravier_maffray_peculiar_chromatic_choosable {V : Type} [Fintype V]
    (H : SimpleGraph V) (hH : IsPeculiar H) :
    ((OAI.LinearListHadwiger.listChromaticNumber H : ℕ) : ℕ∞) = H.chromaticNumber := by sorry

end ClawFreeChoosable
