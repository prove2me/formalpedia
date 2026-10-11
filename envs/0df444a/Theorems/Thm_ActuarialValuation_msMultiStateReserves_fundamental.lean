-- Prove2me | Theorems.Thm_ActuarialValuation_msMultiStateReserves_fundamental
-- name    : ActuarialValuation.msMultiStateReserves_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T14:04:21.864817+00:00
-- url     : https://prove2.me/theorems/1425cad3-ba09-461f-9ab8-128d9e975d89
-- title:
--   Duration-dependent semi-Markov disability and exit valuations: msMultiStateReserves_fundamental
-- statement:
--   The capstone couples exact stochastic population conservation, the full non-stationary Chapman-Kolmogorov identity, origin-state prospective reserve valuation and the duration-sensitive semi-Markov specialisation. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   ΣpT=Σp;(pT)U=p(TU);V_i(d)=b_i+vΣ_jT_ij(d)V_j
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 305. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; Buchardt, Møller and Schmidt, Cash flows and policyholder behaviour in the semi-Markov life insurance setup (2015), https://www.tandfonline.com/doi/full/10.1080/03461238.2013.879919. Parent topic: Finite discrete-time nonstationary and duration-dependent multi-state actuarial benefits, transition probabilities, reserve recursion, disability and surrender cashflows. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msMass
import Definitions.Def_actuarial_msRowMass
import Definitions.Def_actuarial_msStep
import Definitions.Def_actuarial_msTwoStep
import Definitions.Def_actuarial_msApplyTwo
import Definitions.Def_actuarial_msReserveOne
import Definitions.Def_actuarial_msTransitionCost
import Definitions.Def_actuarial_msSemiReserve

namespace ActuarialValuation

theorem msMultiStateReserves_fundamental (p b V : Fin 3 → ℝ) (T U : Fin 3 → Fin 3 → ℝ) (discount : ℝ) (duration : ℕ) (Td : ℕ → Fin 3 → Fin 3 → ℝ) (hT : ∀ i, msRowMass T i=1) (hU : ∀ i, msRowMass U i=1) : (msMass (fun j => msStep p T j)=msMass p) ∧ (∀ k : Fin 3, msApplyTwo p T U k=msStep p (msTwoStep T U) k) ∧ (∀ i : Fin 3, msReserveOne b T V discount i=b i+msTransitionCost T V discount i) ∧ (∀ i : Fin 3, msSemiReserve b Td V discount duration i = msReserveOne b (Td duration) V discount i) := by sorry

end ActuarialValuation
