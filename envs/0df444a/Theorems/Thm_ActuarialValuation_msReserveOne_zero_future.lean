-- Prove2me | Theorems.Thm_ActuarialValuation_msReserveOne_zero_future
-- name    : ActuarialValuation.msReserveOne_zero_future
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T13:59:30.117581+00:00
-- url     : https://prove2.me/theorems/ef6be359-aa7e-4b5d-91c8-6d73eea49fa3
-- title:
--   Transition benefits, annual reserve values and profit: msReserveOne_zero_future
-- statement:
--   Terminal continuation reserves of zero leave the current state benefit alone. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V'_j=0⇒V_i=b_i
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 305. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; Buchardt, Møller and Schmidt, Cash flows and policyholder behaviour in the semi-Markov life insurance setup (2015), https://www.tandfonline.com/doi/full/10.1080/03461238.2013.879919. Parent topic: Finite discrete-time nonstationary and duration-dependent multi-state actuarial benefits, transition probabilities, reserve recursion, disability and surrender cashflows. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msReserveOne

namespace ActuarialValuation

theorem msReserveOne_zero_future (b : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (v : ℝ) (i : Fin 3) : msReserveOne b T (fun _ => 0) v i = b i := by sorry

end ActuarialValuation
