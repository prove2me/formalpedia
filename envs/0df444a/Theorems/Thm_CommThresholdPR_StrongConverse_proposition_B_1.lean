-- Prove2me | Theorems.Thm_CommThresholdPR_StrongConverse_proposition_B_1
-- name    : CommThresholdPR.StrongConverse.proposition_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:47.990861+00:00
-- url     : https://prove2.me/theorems/84c6d196-d7dc-4d48-ac6d-736925271704
-- title:
--   Proposition B.1 — continuity at zero error
-- statement:
--   For every total relation $g$ on nonempty finite input and output alphabets and every joint input law $\mu$,
--   $$\lim_{\varepsilon\downarrow0}\operatorname{IC}_{\mu}(g,\varepsilon)=\operatorname{IC}_{\mu}(g,0).$$
--   The limit is through strictly positive error allowances. The law may have zero entries; full support is not required. The infimum is over all finite randomized binary protocols. This identifies the zero-error endpoint of the information-complexity curve.
--
--   Differences from the source:
--   - encoding: finite public randomness and independent finite private random tapes → finite public seeds and private local kernels on finite binary trees; reason: finite contingent choice tables realize the kernels as independent private tapes; posterior local tape laws recover every source transcript/output law and cost without any uniform bound
--   - encoding: operational infima on nonempty sets bounded below by zero → a guarded real infimum over the entire protocol type; reason: on the source domain input exchange and zero-message protocols ensure nonemptiness and finite information is nonnegative; the fallback is only outside that domain, with these facts left to solvers
--   - encoding: a limit as the error allowance decreases to zero → Tendsto along nhdsWithin 0 (Ioi 0); reason: this is the genuine right-hand limit, without requiring monotone approach sequences
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), Proposition B.1, p. 30, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_Simulation

namespace CommThresholdPR.StrongConverse

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
theorem proposition_B_1 (g : TotalRelation X Y A B) (μ : PMF (X × Y)) :
    Filter.Tendsto (informationComplexity g μ) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (informationComplexity g μ 0)) := by sorry

end CommThresholdPR.StrongConverse
