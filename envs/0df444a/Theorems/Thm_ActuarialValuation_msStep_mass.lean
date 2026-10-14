-- Prove2me | Theorems.Thm_ActuarialValuation_msStep_mass
-- name    : ActuarialValuation.msStep_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:55:24.882198+00:00
-- url     : https://prove2.me/theorems/38e96cc4-ab2a-4983-9095-fd4f3cc3e6c9
-- title:
--   Finite-state transition and probability conservation: msStep_mass
-- statement:
--   A stochastic transition matrix preserves the total expected number of lives. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   Σ_j(pT)_j=Σ_i p_i
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 305. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; Buchardt, Møller and Schmidt, Cash flows and policyholder behaviour in the semi-Markov life insurance setup (2015), https://www.tandfonline.com/doi/full/10.1080/03461238.2013.879919. Parent topic: Finite discrete-time nonstationary and duration-dependent multi-state actuarial benefits, transition probabilities, reserve recursion, disability and surrender cashflows. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msMass
import Definitions.Def_actuarial_msRowMass
import Definitions.Def_actuarial_msStep

namespace ActuarialValuation

theorem msStep_mass (p : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (hT : ∀ i, msRowMass T i = 1) : msMass (fun j => msStep p T j) = msMass p := by sorry

end ActuarialValuation
