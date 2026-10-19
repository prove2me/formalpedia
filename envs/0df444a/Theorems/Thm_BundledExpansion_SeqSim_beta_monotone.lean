-- Prove2me | Theorems.Thm_BundledExpansion_SeqSim_beta_monotone
-- name    : BundledExpansion.SeqSim.beta_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:16.589213+00:00
-- url     : https://prove2.me/theorems/6ea56635-eeee-4908-a3a4-7cde78ef0fe5
-- title:
--   Proposition 1 — joint optimum increases with β
-- statement:
--   On the model’s admissible multiplier interval $[1,2]$, the optimal simultaneous-replenishment cost increases strictly with $\beta$:
--
--   $$
--   1\le\beta_1<\beta_2\le2\quad\Longrightarrow\quad V_{\mathrm{sim}}(\beta_1)<V_{\mathrm{sim}}(\beta_2).
--   $$
--
--   This establishes uniqueness of any cost crossing with the sequential optimum. **Formalization Note** The paper’s last paragraph prints $[0,1]$, while its model specifies $[1,2]$; the statement uses the model interval. Every policy has at least one expansion and $A>0$. Lean indices 0 and 1 are the paper’s 1 and 2.
-- source:
--   Arbabian, Chen & Moinzadeh, Capacity Expansions with Bundled Supplies of Attributes, SSRN 3085349 (manuscript of April 14, 2019), https://ssrn.com/abstract=3085349, p. 14 (PDF 15), paragraph following Proposition 1

import Mathlib
import Definitions.Def_BundledExpansion_SeqSim_Model

namespace BundledExpansion.SeqSim

theorem beta_monotone (P : Params) (hS : P.Standing)
    (hR : P.Regular) (hG : P.RatioGuard) :
    StrictMonoOn (optSim P) (Set.Icc (1 : ℝ) 2) := by sorry

end BundledExpansion.SeqSim
