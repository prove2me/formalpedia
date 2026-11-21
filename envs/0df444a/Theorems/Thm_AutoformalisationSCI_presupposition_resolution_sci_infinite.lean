-- Prove2me | Theorems.Thm_AutoformalisationSCI_presupposition_resolution_sci_infinite
-- name    : AutoformalisationSCI.presupposition_resolution_sci_infinite
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T15:36:18.053011+00:00
-- url     : https://prove2.me/theorems/dba8ad7e-8fb1-43a8-ad49-cc0eeec3b97c
-- title:
--   Main result — SCI = ∞ for presupposition resolution
-- statement:
--   **Main result (Appendix A.2.1, pp. 22–23).** Fix $k\ge 9$ and any family of computable enumerations of integer-coefficient polynomials, one for each level. Consider the combined presupposition-resolution problem: given $e\in\mathbb N$ and a level $l\ge 2$, decide whether $\{n:B_e^{(l)}(n)\}$ is nonempty. Then
--   $$\mathrm{SCI}_A(\text{combined problem})=\infty.$$
--
--   This is the precise form of the paper's headline claim that *providing semantically faithful AI autoformalisation is harder than any computational problem*: a trustworthy autoformaliser that always outputs either a semantically faithful translation or "this statement cannot be translated" must resolve the above question for every $e$ and $l\ge 2$, a problem harder than every problem of finite SCI. It follows from Corollary A.5, since a finite tower for the combined problem would restrict to a tower of the same height for each fixed level $l$, contradicting $\mathrm{SCI}_A(\Xi_{d_l})=l$ for $l$ larger than that height.
-- source:
--   A. Bastounis, F. Circelli, A. C. Hansen, Navier–Stokes lost in translation, arXiv:2610.08144 (2026), https://arxiv.org/abs/2610.08144. Appendix A.2.1, pp. 22–23; abstract; §4.1 and §5.

import Mathlib
import Definitions.Def_AutoformalisationSCI_SCI
import Definitions.Def_AutoformalisationSCI_Poly

open AutoformalisationSCI

namespace AutoformalisationSCI

theorem presupposition_resolution_sci_infinite (k : ℕ) (hk : 9 ≤ k)
    (E : ∀ l : ℕ, ComputablePolyEnum (l - 1 + k)) :
    SCI_A (combinedProblem k E) = ⊤ := by sorry

end AutoformalisationSCI
