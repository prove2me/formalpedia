-- Prove2me | Theorems.Thm_ActuarialValuation_msSemiReserve_same_duration
-- name    : ActuarialValuation.msSemiReserve_same_duration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T14:02:24.05297+00:00
-- url     : https://prove2.me/theorems/b8410217-7c97-4824-839f-962b1cc104a6
-- title:
--   Duration-dependent semi-Markov disability and exit valuations: msSemiReserve_same_duration
-- statement:
--   No change in elapsed duration yields zero pure-duration reserve movement. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   ΔV(d,d)=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 305. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; Buchardt, Møller and Schmidt, Cash flows and policyholder behaviour in the semi-Markov life insurance setup (2015), https://www.tandfonline.com/doi/full/10.1080/03461238.2013.879919. Parent topic: Finite discrete-time nonstationary and duration-dependent multi-state actuarial benefits, transition probabilities, reserve recursion, disability and surrender cashflows. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msSemiReserve

namespace ActuarialValuation

theorem msSemiReserve_same_duration (b V : Fin 3 → ℝ) (T : ℕ → Fin 3 → Fin 3 → ℝ) (v : ℝ) (d : ℕ) (i : Fin 3) : msSemiReserve b T V v d i - msSemiReserve b T V v d i = 0 := by sorry

end ActuarialValuation
