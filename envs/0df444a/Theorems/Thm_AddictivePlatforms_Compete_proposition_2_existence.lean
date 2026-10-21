-- Prove2me | Theorems.Thm_AddictivePlatforms_Compete_proposition_2_existence
-- name    : AddictivePlatforms.Compete.proposition_2_existence
-- status  : Proved
-- author  : @queelius
-- created : 2026-10-20T17:38:56.202674+00:00
-- url     : https://prove2.me/theorems/34c2d586-1c16-4767-85da-bcc834217971
-- title:
--   Proposition 2, existence part — a positive symmetric subgame-perfect equilibrium for every positive attention cap
-- statement:
--   For K ≥ 2 platforms, under the existing Standing assumptions and UncOptExists qualification of the attention-competition model, every positive finite or infinite attention cap admits a positive addictiveness level d* satisfying equation (3). The symmetric profile in which every platform chooses d* is supported by a pure-strategy subgame-perfect equilibrium. The consumer strategy best responds at every nonnegative profile, and no platform can increase its attention payoff through any unilateral nonnegative deviation.
--
--   This is the complete existence clause of Proposition 2, proved in Appendix B, Step 2. It does not assert uniqueness of equilibrium profiles or the monopoly/duopoly comparisons of Proposition 3. The existing platform qualifications, including strict concavity in attention, C(0)=0, uncapped-optimum existence and positive attention cap, are retained.
--
--   Source mathematics: Shota Ichihashi and Byung-Cheol Kim. The shared formal model and qualifications are due to mikedeng1, with statement review by Shuze Chen. Alexander Richard Towell (queelius), with substantial OpenAI Codex assistance, isolates and formally verifies this complete supporting obligation from the existing full Proposition 2. No mathematical novelty or independent human proof review is claimed.
-- source:
--   Ichihashi & Kim, Addictive Platforms, Bank of Canada Staff Working Paper 2022-16 (1 April 2022), Proposition 2 p.11, Appendix B Step 2 pp.31–32. https://www.bankofcanada.ca/wp-content/uploads/2022/04/swp2022-16.pdf . Existence clause of existing platform target https://prove2.me/theorems/4f26bfb9-a594-4bbb-b333-24f8438c0760 .

import Mathlib
import Definitions.Def_AddictivePlatforms_Compete_Model
open AddictivePlatforms.Compete
open scoped ENNReal

namespace AddictivePlatforms.Compete

theorem proposition_2_existence (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    (K : ℕ) (hK : 2 ≤ K) (hE : UncOptExists u C K)
    (Abar : ℝ≥0∞) (hAbar : 0 < Abar) :
    ∃ dstar : ℝ, 0 < dstar ∧ Eq3 u C Abar K dstar ∧
      ∃ σ : ConsumerStrategy K, IsSPE u C Abar (fun _ : Fin K => dstar) σ := by sorry

end AddictivePlatforms.Compete
