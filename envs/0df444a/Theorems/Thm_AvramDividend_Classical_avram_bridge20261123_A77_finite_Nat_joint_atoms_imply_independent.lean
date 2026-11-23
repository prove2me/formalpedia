-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_finite_Nat_joint_atoms_imply_independent
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_finite_Nat_joint_atoms_imply_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T17:37:10.179352+00:00
-- url     : https://prove2.me/theorems/4123dd92-5095-42ab-ad8d-e08e6ba12fb7
-- title:
--   Finite Nat-valued random-family independence from every joint singleton probability factorisation
-- statement:
--   A measurable finite family of Nat-valued random variables on a probability space is jointly independent if the probability of each joint point cylinder factors as the product of marginal point probabilities. Prove directly by Mathlib independence iff the joint law equals the product law, extensionality of measures on countable spaces via singleton sets and the finite product measure singleton identity. This is a generic measurable criterion; it does not assume Poisson law or invent stochastic independence for the original Lévy source.
-- source:
--   Mathlib Probability.Independence.Basic.iIndepFun_iff_map_fun_eq_pi_map, Measure.ext_of_singleton, Measure.pi_singleton, and Avram A77 original physical finite spatial joint-count core db5c4c1b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_finite_Nat_joint_atoms_imply_independent
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (K : Fin n → Ω → ℕ)
    (hMeas : ∀ i, Measurable (K i))
    (hAtoms : ∀ counts : Fin n → ℕ,
      P {ω : Ω | ∀ i, K i ω = counts i} =
        ∏ i : Fin n, P {ω : Ω | K i ω = counts i}) :
    iIndepFun K P := by sorry
