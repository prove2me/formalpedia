-- Prove2me | Theorems.Thm_BitcoinOligopoly_EoS_f_decreasing
-- name    : BitcoinOligopoly.EoS.f_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:40.13646+00:00
-- url     : https://prove2.me/theorems/0e2e9940-e6d9-44a8-9026-5090b80fd4f2
-- title:
--   Proof of Proposition 1 — decrease of the share-shape function
-- statement:
--   Let $\alpha\ge1$ and define $f_\alpha(x)=x^{1-1/\alpha}(1-x)$. On the open interval used in the proof of Proposition 1,
--
--   $$
--   f_\alpha\text{ is strictly decreasing on }(1-1/\alpha,1).
--   $$
--
--   This analytic fact converts the order of positive equilibrium investments into the reverse order of their unit costs.
--
--   **Formalization Note** The paper says “decreasing” and establishes a strictly negative derivative on this interval. The Lean statement uses strict decrease on the paper's open interval; the left endpoint is handled separately when this fact is used.
-- source:
--   Arnosti & Weinberg, Bitcoin: A Natural Oligopoly, arXiv:1811.08572v1, p. 10 (PDF 11), proof of Proposition 1, after definition of f

import Mathlib
import Definitions.Def_BitcoinOligopoly_EoS_Model

namespace BitcoinOligopoly.EoS

/-- The strict decrease asserted in the proof of Proposition 1, p. 10 (PDF 11). -/
theorem f_decreasing (α : ℝ) (hα : 1 ≤ α) :
    StrictAntiOn (fShape α) (Set.Ioo (1 - 1 / α) 1) := by sorry

end BitcoinOligopoly.EoS
