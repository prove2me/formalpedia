-- Prove2me | Theorems.Thm_ActuarialValuation_msTwoStep_zero_right
-- name    : ActuarialValuation.msTwoStep_zero_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:55:54.29621+00:00
-- url     : https://prove2.me/theorems/b992e9f0-2852-43d9-bfd7-7bf510a036f1
-- title:
--   Finite-state transition and probability conservation: msTwoStep_zero_right
-- statement:
--   If all second-period transitions vanish, all two-period mass is zero. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   (T0)_{ik}=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 305. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; Buchardt, Møller and Schmidt, Cash flows and policyholder behaviour in the semi-Markov life insurance setup (2015), https://www.tandfonline.com/doi/full/10.1080/03461238.2013.879919. Parent topic: Finite discrete-time nonstationary and duration-dependent multi-state actuarial benefits, transition probabilities, reserve recursion, disability and surrender cashflows. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msTwoStep

namespace ActuarialValuation

theorem msTwoStep_zero_right (T : Fin 3 → Fin 3 → ℝ) (i k : Fin 3) : msTwoStep T (fun _ _ => 0) i k = 0 := by sorry

end ActuarialValuation
