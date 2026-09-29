-- Prove2me | solution 1 for mme_stothers_phi233_uniform_entropy_stability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:45:49.751033+00:00
-- url     : https://prove2.me/submissions/ee2cbf5f-f6f7-410a-9886-2834c6ea5728

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Algebra.Order.Field
import Theorems.Thm_mme_stothers_phi233_entropy_tangent_stability

open Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

/-- Every normalized competitor with the marginals of a profile converging to
a positive stationary `phi_233` profile has entropy at most the target
profile entropy plus an arbitrarily small error, uniformly and eventually. -/
theorem solution
    (a b c d : ℝ) (A B C D X Y Z W : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (htotal : 2 * a + b + c + d = 1)
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0)
    (hA : Tendsto A atTop (nhds a))
    (hB : Tendsto B atTop (nhds b))
    (hC : Tendsto C atTop (nhds c))
    (hD : Tendsto D atTop (nhds d))
    (hX : ∀ n, 0 ≤ X n) (hY : ∀ n, 0 ≤ Y n)
    (hZ : ∀ n, 0 ≤ Z n) (hW : ∀ n, 0 ≤ W n)
    (htotalX : ∀ n, 2 * X n + Y n + Z n + W n = 1)
    (hsigmaX : ∀ n, 2 * X n + Y n = 2 * A n + B n)
    (hmuX : ∀ n, X n + Z n = A n + C n) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        4 * Real.negMulLog (X n / 2) +
              2 * Real.negMulLog (Y n / 2) +
              2 * Real.negMulLog (Z n / 2) +
              2 * Real.negMulLog (W n / 2) ≤
          4 * Real.negMulLog (A n / 2) +
              2 * Real.negMulLog (B n / 2) +
              2 * Real.negMulLog (C n / 2) +
              2 * Real.negMulLog (D n / 2) + ε := by
  intro ε hε
  let T : ℝ :=
    4 * Real.negMulLog (a / 2) +
      2 * Real.negMulLog (b / 2) +
      2 * Real.negMulLog (c / 2) +
      2 * Real.negMulLog (d / 2)
  let lambdaSigma : ℝ :=
    (-Real.log (b / 2) - 1) - (-Real.log (d / 2) - 1)
  let lambdaMu : ℝ :=
    (-Real.log (c / 2) - 1) - (-Real.log (d / 2) - 1)
  let targetEntropy : ℕ → ℝ := fun n ↦
    4 * Real.negMulLog (A n / 2) +
      2 * Real.negMulLog (B n / 2) +
      2 * Real.negMulLog (C n / 2) +
      2 * Real.negMulLog (D n / 2)
  let upper : ℕ → ℝ := fun n ↦
    T + lambdaSigma * ((2 * A n + B n) - (2 * a + b)) +
      lambdaMu * ((A n + C n) - (a + c))
  have hA2 : Tendsto (fun n ↦ A n / 2) atTop (nhds (a / 2)) :=
    hA.div_const 2
  have hB2 : Tendsto (fun n ↦ B n / 2) atTop (nhds (b / 2)) :=
    hB.div_const 2
  have hC2 : Tendsto (fun n ↦ C n / 2) atTop (nhds (c / 2)) :=
    hC.div_const 2
  have hD2 : Tendsto (fun n ↦ D n / 2) atTop (nhds (d / 2)) :=
    hD.div_const 2
  have hTarget : Tendsto targetEntropy atTop (nhds T) := by
    dsimp only [targetEntropy, T]
    exact
      ((((Real.continuous_negMulLog.tendsto (a / 2)).comp hA2).const_mul 4).add
        (((Real.continuous_negMulLog.tendsto (b / 2)).comp hB2).const_mul 2)).add
        (((Real.continuous_negMulLog.tendsto (c / 2)).comp hC2).const_mul 2) |>.add
        (((Real.continuous_negMulLog.tendsto (d / 2)).comp hD2).const_mul 2)
  have hSigma : Tendsto (fun n ↦ 2 * A n + B n)
      atTop (nhds (2 * a + b)) := (hA.const_mul 2).add hB
  have hMu : Tendsto (fun n ↦ A n + C n)
      atTop (nhds (a + c)) := hA.add hC
  have hUpper : Tendsto upper atTop (nhds T) := by
    dsimp only [upper]
    convert
      tendsto_const_nhds.add
        ((hSigma.sub tendsto_const_nhds).const_mul lambdaSigma) |>.add
        ((hMu.sub tendsto_const_nhds).const_mul lambdaMu) using 1;
      ring
  have hError : Tendsto (fun n ↦ upper n - targetEntropy n)
      atTop (nhds 0) := by
    convert hUpper.sub hTarget using 1
    · ring
  filter_upwards [hError.eventually_lt_const hε] with n hn
  have hpoint := mme_stothers_phi233_entropy_tangent_stability
    a b c d (X n) (Y n) (Z n) (W n)
    (2 * a + b) (a + c) (2 * A n + B n) (A n + C n)
    ha hb hc hd (hX n) (hY n) (hZ n) (hW n)
    htotal (htotalX n) rfl rfl (hsigmaX n) (hmuX n) hstation
  have hpoint' :
      4 * Real.negMulLog (X n / 2) +
            2 * Real.negMulLog (Y n / 2) +
            2 * Real.negMulLog (Z n / 2) +
            2 * Real.negMulLog (W n / 2) ≤ upper n := by
    simpa only [upper, T, lambdaSigma, lambdaMu] using hpoint
  linarith
