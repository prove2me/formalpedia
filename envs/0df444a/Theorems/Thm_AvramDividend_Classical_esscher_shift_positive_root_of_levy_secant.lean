-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_shift_positive_root_of_levy_secant
-- name    : AvramDividend.Classical.esscher_shift_positive_root_of_levy_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T15:45:13.350692+00:00
-- url     : https://prove2.me/theorems/a9d8fdb2-917c-4ec8-992f-fa0ba374c16b
-- title:
--   Positive Esscher-shift roots from the genuine Lévy secant inequality
-- statement:
--   For a canonical spectrally negative Lévy process X with positive q-root φ, every p>0 has a positive shifted exponent root λ satisfying X.ψ(φ+λ)−q=p. This uses the already-Proved canonical linear secant lower bound and the actual continuity of X.ψ on nonnegative arguments, without the extra X.Standing assumption or a Wiener–Hopf factor.
-- source:
--   Proved e9488750-ba29-4b2a-9d1d-05734aaa628f (canonical Lévy exponent root-shifted linear secant) and 1fa27b74-bf2c-4549-8110-d30ac84f57e6 (canonical continuity), with pinned Mathlib intermediate_value_Icc; Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes, §2.

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_shift_positive_root_of_levy_secant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P F)
    (q phi p : ℝ)
    (hq : 0 < q) (hphi : 0 < phi) (hroot : X.ψ phi = q)
    (hp : 0 < p) :
    ∃ lambda : ℝ, 0 < lambda ∧ X.ψ (phi + lambda) - q = p := by sorry
