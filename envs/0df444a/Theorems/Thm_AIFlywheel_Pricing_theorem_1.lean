-- Prove2me | Theorems.Thm_AIFlywheel_Pricing_theorem_1
-- name    : AIFlywheel.Pricing.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:54.386102+00:00
-- url     : https://prove2.me/theorems/eda4842e-3136-4217-b7c7-ac29d7357824
-- title:
--   Theorem 1: data impact determines the direction of data distortion
-- statement:
--   Let $\delta^*$ be the low-accuracy first-period data quantity of an optimal contract in Problem (6)–(9), and let $\delta^{FB}$ be that of an optimal first-best plan, with payments fixed at $\kappa$ and incentive constraints removed. Assume both prices give interior data quantities. On the feasible dataset interval:
--   $$
--   \begin{aligned}
--   \rho\text{ constant} &\Longrightarrow \delta^*=\delta^{FB},\\
--   \rho\text{ strictly increasing} &\Longrightarrow \delta^*>\delta^{FB},\\
--   \rho\text{ strictly decreasing} &\Longrightarrow \delta^*<\delta^{FB}.
--   \end{aligned}
--   $$
--   Thus the data impact of effort determines whether moral hazard leads the firm to collect the first-best amount, more data, or less data.
--
--   **Formalization Note.** Both optima are global optima of the full problems, including payment and incentive constraints for the contract. The paper assumes interior prices on p. 11. The model also makes positive low accuracy and $\pi_w<1$ explicit to preserve uniqueness; differentiability replaces stronger smoothness used in the source's later proofs.
-- source:
--   Gurkan & de Véricourt, Contracting, Pricing and Data Collection under the AI Flywheel Effect, ESMT Working Paper 20-01 (R3), August 17, 2021, p. 14 (PDF 15), Theorem 1; proof p. 29 (PDF 30).

import Mathlib
import Definitions.Def_AIFlywheel_Pricing_Model

namespace AIFlywheel.Pricing

/-- Theorem 1, p. 14: data-impact monotonicity determines data distortion. -/
theorem theorem_1 (P : Params) (hP : P.Standing)
    (s : Plan) (hs : IsOptimal P s)
    (fh fl : ℝ) (hf : IsFBOptimal P fh fl)
    (hint : s.δ1l ∈ Set.Ioo 0 P.ν ∧ fl ∈ Set.Ioo 0 P.ν) :
    ((∃ c : ℝ, ∀ d ∈ Set.Icc P.dmin P.dmax, dataImpact P d = c) →
      s.δ1l = fl) ∧
    (StrictMonoOn (dataImpact P) (Set.Icc P.dmin P.dmax) → fl < s.δ1l) ∧
    (StrictAntiOn (dataImpact P) (Set.Icc P.dmin P.dmax) → s.δ1l < fl) := by sorry

end AIFlywheel.Pricing
