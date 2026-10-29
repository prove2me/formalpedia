-- Prove2me | Theorems.Thm_ClickomaniaNPC_ThreeColor_theorem_15
-- name    : ClickomaniaNPC.ThreeColor.theorem_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T04:13:33.264+00:00
-- url     : https://prove2.me/theorems/a9880aa5-dfe0-485f-9052-a153e7812e18
-- title:
--   Theorem 15 — Clickomania is NP-complete with five columns and three colors
-- statement:
--   Deciding whether all blocks of an initially full rectangular Clickomania puzzle can be removed is NP-complete. This remains NP-complete for initially five-column rectangles over a palette of three available colors, with arbitrary finite height and no requirement that every color occur.
--
--   A click removes a whole maximal edge-connected monochromatic component of at least two blocks. Surviving blocks settle vertically without changing order; empty columns disappear without changing the order of the remaining columns. Solvability means that some finite legal play removes every block.
--
--   Writing L for the unrestricted encoded solvability language and L₅,₃ for its width-five, palette-three restriction, the target is
--
--   $$\operatorname{NPComplete}(L) \;\land\; \operatorname{NPComplete}(L_{5,3}).$$
--
--   Each assertion includes membership in NP and a polynomial-time many-one reduction from every NP language over any finite nonempty alphabet, measured by actual Turing-machine steps in input word length. The theorem is unconditional: SAT hardness, a correct reduction and a correct verifier are not hypotheses. The goal is an open statement, not a completed proof.
--
--   Differences from the source:
--   - encoding: finite full rectangular boards with colors and the stated click rules → ordered bottom-to-top column lists, natural color labels below the declared palette, maximal components defined by finite monochromatic edge paths, stable deletion and empty-column removal; reason: this represents the same positions and moves; input rectangles and later unequal-height states remain distinct
--   - encoding: deciding whether a given puzzle can be solved, without a fixed bit syntax → languages of canonical self-delimiting binary dimension and palette headers followed by explicit individual cell codes; malformed words are rejected; reason: a concrete finite-alphabet input convention is needed for machine complexity; no block sequence is compressed
--   - encoding: remove all blocks, with zero dimensions left implicit → zero-area inputs are already solved, height-zero boards are normalized to the empty list, and a zero palette is allowed only for empty inputs; reason: explicit empty-instance conventions retain all nonempty source instances and add no height lower bound
--   - encoding: NP-complete, even with only five columns and three colors → a conjunction of CookPvsNP.NPComplete for the unrestricted language and for initial width exactly five and palette exactly three, with unused colors allowed; reason: the published finite-alphabet machine definitions express both NP membership and polynomial-time many-one hardness; the conjunction retains both source clauses
-- source:
--   Biedl, Demaine, Demaine, Fleischer, Jacobsen and Munro, The Complexity of Clickomania, arXiv:cs/0107031v1 (21 July 2001), Theorem 15, p. 11; operational model, section 1, p. 1. https://arxiv.org/abs/cs/0107031v1

import Definitions.Def_ClickomaniaNPC_ThreeColor_Grid
import Definitions.Def_ClickomaniaNPC_ThreeColor_Play
import Definitions.Def_ClickomaniaNPC_ThreeColor_Code
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ClickomaniaNPC_ThreeColor_Languages

namespace ClickomaniaNPC.ThreeColor

/-- Biedl et al., arXiv:cs/0107031v1, Theorem 15, p. 11. -/
theorem theorem_15 :
    CookPvsNP.NPComplete clickomaniaLanguage ∧
    CookPvsNP.NPComplete fiveThreeLanguage := by sorry

end ClickomaniaNPC.ThreeColor
