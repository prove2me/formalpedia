-- Prove2me | Theorems.Thm_ActuarialValuation_msSemiReserve_duration_change
-- name    : ActuarialValuation.msSemiReserve_duration_change
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T14:02:09.744976+00:00
-- url     : https://prove2.me/theorems/b902a10d-eedd-4d74-b590-0e6c57d00793
-- title:
--   Duration-dependent semi-Markov disability and exit valuations: msSemiReserve_duration_change
-- statement:
--   Valuation differences by disability duration arise from changed transition weights on future benefit reserves. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V(d₂)-V(d₁)=vΣ ΔT_ij V_j
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 305. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; Buchardt, Møller and Schmidt, Cash flows and policyholder behaviour in the semi-Markov life insurance setup (2015), https://www.tandfonline.com/doi/full/10.1080/03461238.2013.879919. Parent topic: Finite discrete-time nonstationary and duration-dependent multi-state actuarial benefits, transition probabilities, reserve recursion, disability and surrender cashflows. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msSemiReserve

namespace ActuarialValuation

theorem msSemiReserve_duration_change (b V : Fin 3 → ℝ) (T : ℕ → Fin 3 → Fin 3 → ℝ) (v : ℝ) (d₁ d₂ : ℕ) (i : Fin 3) : msSemiReserve b T V v d₂ i - msSemiReserve b T V v d₁ i = v*(∑ j : Fin 3, (T d₂ i j-T d₁ i j)*V j) := by sorry

end ActuarialValuation
