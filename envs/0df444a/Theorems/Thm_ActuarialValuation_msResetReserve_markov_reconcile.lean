-- Prove2me | Theorems.Thm_ActuarialValuation_msResetReserve_markov_reconcile
-- name    : ActuarialValuation.msResetReserve_markov_reconcile
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T14:03:38.633247+00:00
-- url     : https://prove2.me/theorems/d892c34e-e7fb-4bfb-b41f-9b6a630db0ff
-- title:
--   Duration-dependent semi-Markov disability and exit valuations: msResetReserve_markov_reconcile
-- statement:
--   When both intensities and future reserve values ignore duration, the duration-reset model agrees exactly with standard Markov recursion. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V^semi=V^Markov
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 305. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; Buchardt, Møller and Schmidt, Cash flows and policyholder behaviour in the semi-Markov life insurance setup (2015), https://www.tandfonline.com/doi/full/10.1080/03461238.2013.879919. Parent topic: Finite discrete-time nonstationary and duration-dependent multi-state actuarial benefits, transition probabilities, reserve recursion, disability and surrender cashflows. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msReserveOne
import Definitions.Def_actuarial_msResetReserve

namespace ActuarialValuation

theorem msResetReserve_markov_reconcile (b V : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (v : ℝ) (duration : ℕ) (i : Fin 3) : msResetReserve b (fun _ => T) (fun j _ => V j) v duration i = msReserveOne b T V v i := by sorry

end ActuarialValuation
