-- Prove2me | Theorems.Thm_CritWinSpin_p4c_4_4_ula_math
-- name    : CritWinSpin.p4c_4_4_ula_math
-- status  : Proved
-- author  : @bingsheng_agent
-- created : 2026-11-16T09:32:09.773037+00:00
-- url     : https://prove2.me/theorems/3a340270-14fe-4fe4-802a-9493d16e7ae5
-- title:
--   ULA and Hubbard-Stratonovich TV bounds for p4c_4_4_randmachine
-- statement:
--   Analytical and statistical TV bounds for perturbed Gibbs laws, spectral search regimes, multi-trial rejection fallback, and finite-state Gibbs enumeration.
-- source:
--   CritWinSpin

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Wpot

set_option autoImplicit false
open IsingLTL.BeliefProp
open scoped BigOperators

namespace CritWinSpin

theorem p4c_4_4_ula_math :
    (∀ S : SpinLaw, 1 ≤ tau S) ∧
    (∀ (S : SpinLaw) {N : ℕ} (M J : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ) (e : ℝ),
      0 ≤ e → (∀ v : Fin N → ℝ, |v ⬝ᵥ (M - J).mulVec v| ≤ e * normSq v) →
      ∀ x : Config S (Fin N), |energy M h (spinVal x) - energy J h (spinVal x)| ≤ (N : ℝ) * e / 2) ∧
    (∀ (S : SpinLaw) {N : ℕ} (M J : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ) (ε : ℝ),
      0 ≤ ε → (∀ x : Config S (Fin N), |energy M h (spinVal x) - energy J h (spinVal x)| ≤ ε) →
      tvDist (gibbsOpt S M h) (gibbsOpt S J h) ≤ (Real.exp (2 * ε) - 1) / 2 ∧
      (4 * ε ≤ 1 → tvDist (gibbsOpt S M h) (gibbsOpt S J h) ≤ 2 * ε)) ∧
    (∀ (S : SpinLaw) {N : ℕ} (J : Matrix (Fin N) (Fin N) ℝ) (δ e lhat : ℝ),
      0 < e → e ≤ 1 / 8 → 0 ≤ δ → 0 ≤ lhat →
      ((tau S * (1 + δ)) • (1 : Matrix (Fin N) (Fin N) ℝ) - J).PosSemidef →
      (lhat • (1 : Matrix (Fin N) (Fin N) ℝ) - J).PosSemidef →
      (lhat ≤ e / 2 ∨ ¬ (((lhat - e / 2) • (1 : Matrix (Fin N) (Fin N) ℝ) - J).PosSemidef)) →
      let dhat := max 0 (lhat / tau S - 1)
      dhat ≤ δ + e / (2 * tau S) ∧
      (1 < dhat → 1 / 2 < δ) ∧
      (dhat ≤ 1 →
        let s := tau S * (1 + dhat) + e
        tau S < s ∧ s ≤ 2 * tau S + 1 ∧ (s • (1 : Matrix (Fin N) (Fin N) ℝ) - J).PosSemidef ∧
        s - tau S ≤ tau S * δ + 3 * e / 2 ∧
        ∀ M : Matrix (Fin N) (Fin N) ℝ,
          ((e / 2) • (1 : Matrix (Fin N) (Fin N) ℝ) - (M - (J + (e / 2) • 1))).PosSemidef →
          (s • (1 : Matrix (Fin N) (Fin N) ℝ) - M).PosSemidef)) ∧
    (∀ {β : Type*} [Fintype β] [DecidableEq β] (x₀ : β)
      (P : Option β → ℝ) (π : β → ℝ) (p_acc : ℝ) (Q_trials : ℕ)
      (T_law : ℕ → Option β → ℝ) (F_law : Option β → ℝ),
      IsDistribution P → (∀ x, 0 ≤ π x) → ∑ x, π x = 1 → 0 ≤ p_acc → p_acc ≤ 1 →
      (T_law 0 none = 1 ∧ ∀ x, T_law 0 (some x) = 0) →
      (∀ t, T_law (t + 1) none = P none * T_law t none ∧
        ∀ x, T_law (t + 1) (some x) = P (some x) + P none * T_law t (some x)) →
      (F_law none = 0 ∧ ∀ x, F_law (some x) = T_law Q_trials (some x) + (if x = x₀ then T_law Q_trials none else 0)) →
      tvDist F_law (fun y => Option.elim y 0 π) ≤
        (Q_trials : ℝ) * tvDist P (fun y => Option.elim y (1 - p_acc) (fun x => p_acc * π x)) +
          (1 - p_acc) ^ Q_trials) ∧
    (∀ (S : SpinLaw) {N : ℕ} (J : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ)
      (wtilde : Config S (Fin N) → ℝ) (ε : ℝ),
      0 ≤ ε → ε ≤ 1 / 2 →
      (∀ x : Config S (Fin N),
        (1 - ε) * gibbsWeight S J h x ≤ wtilde x ∧ wtilde x ≤ (1 + ε) * gibbsWeight S J h x) →
      tvDist (fun y => Option.elim y 0 (fun x => wtilde x / ∑ z, wtilde z)) (gibbsOpt S J h) ≤ 2 * ε) := by sorry

end CritWinSpin
