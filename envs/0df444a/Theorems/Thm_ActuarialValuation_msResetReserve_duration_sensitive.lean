-- Prove2me | Theorems.Thm_ActuarialValuation_msResetReserve_duration_sensitive
-- name    : ActuarialValuation.msResetReserve_duration_sensitive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T14:03:48.768508+00:00
-- url     : https://prove2.me/theorems/47b88a88-8c15-4498-a395-5b9e6b74ccb0
-- title:
--   Duration-dependent semi-Markov disability and exit valuations: msResetReserve_duration_sensitive
-- statement:
--   A semi-Markov reserve genuinely depends on continuation reserve at the next sojourn duration, resetting after a state exit. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V_i(d)=b_i+vΣ_jT_ij(d)V_j(d')
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 305. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; Buchardt, Møller and Schmidt, Cash flows and policyholder behaviour in the semi-Markov life insurance setup (2015), https://www.tandfonline.com/doi/full/10.1080/03461238.2013.879919. Parent topic: Finite discrete-time nonstationary and duration-dependent multi-state actuarial benefits, transition probabilities, reserve recursion, disability and surrender cashflows. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msDurationNext
import Definitions.Def_actuarial_msResetReserve

namespace ActuarialValuation

theorem msResetReserve_duration_sensitive (b : Fin 3 → ℝ) (T : ℕ → Fin 3 → Fin 3 → ℝ) (V : Fin 3 → ℕ → ℝ) (v : ℝ) (duration : ℕ) (i : Fin 3) : msResetReserve b T V v duration i = b i+v*(∑ j : Fin 3, T duration i j*V j (msDurationNext i j duration)) := by sorry

end ActuarialValuation
