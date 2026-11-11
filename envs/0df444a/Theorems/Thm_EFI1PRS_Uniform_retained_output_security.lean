-- Prove2me | Theorems.Thm_EFI1PRS_Uniform_retained_output_security
-- name    : EFI1PRS.Uniform.retained_output_security
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T05:02:36.02287+00:00
-- url     : https://prove2.me/theorems/381db005-47cc-4166-81b7-87246d965aec
-- title:
--   §5.1 — security of retained outputs
-- statement:
--   For any amplified EFI pair and the actual source construction, $\mathcal H_N$ is computationally indistinguishable from $\mathcal H_0$, and $\mathcal H_0$ is exactly maximally mixed on all raw seeds, shifts and retained columns. For every non-uniform polynomial-size quantum-advice adversary $T$, uniformly after a threshold independent of the test,
--
--   $$\operatorname{Adv}_T(\mathcal H_N,\mathcal H_0)\le\sum_{i=1}^{N}\operatorname{Adv}_T(\mathcal H_i,\mathcal W_i)+N(2^{-\lambda}+2^{-\lambda^2}),\qquad\mathcal H_N\approx_c\mathcal H_0.$$
--
--   The number of columns depends on the security parameter. The hiding conclusion covers all allowed advice states and does not assume the computational hybrid sum is negligible.
--
--   Differences from the source:
--   - encoding: positive unary security parameters and ordinary finite-gate QPT circuits → zero-based wire indices, explicit finite H/S/T/X/Z/CNOT descriptions, coherent workspace and final partial traces; reason: these give explicit circuit semantics and charge all descriptions; the general simulation/compilation bridge remains a proof obligation, not a primitive assumption
--   - encoding: a coherent purification padded to any power-of-two width M at least four, with registers ordered R,F,E,padding → the actual circuit purification, an explicit output/complement wire permutation, and M equal to 2^(Nat.log2(max 4 (2+work))+1); reason: this selects a permitted efficient padding and fixes its wire order; no purification property or entropy estimate is assumed
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, §5.1, PDF/printed p. 14

import Definitions.Def_EFI1PRS_Uniform_Generator

/-! Rishabh Batra, EFI ⇔ 1PRS, pinned October 2026 STOC submission #273.
Statement-preparation draft; proof is a future solver obligation. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

theorem retained_output_security (g : PairPreparation) (hg : IsAmplifiedEFI g) :
    ComputationallyIndistinguishable (fun sec => H g sec (windowLength (sourceWidth g sec)))
      (fun sec => H g sec 0) ∧
    (∀ sec, 1 ≤ sec → H g sec 0 = maximallyMixed (retainedWidth g sec)) ∧
    ∃ threshold : ℕ, ∀ sec, threshold ≤ sec → 1 ≤ sec →
      ∀ T : AdvisedPreparation (retainedWidth g) (fun _ => 1), T.IsPolynomial →
        |T.acceptance sec (H g sec (windowLength (sourceWidth g sec))) - T.acceptance sec (H g sec 0)| ≤
          (∑ i ∈ Finset.range (windowLength (sourceWidth g sec)),
            |T.acceptance sec (H g sec (i+1)) - T.acceptance sec (W g sec (i+1))|) +
            (windowLength (sourceWidth g sec) : ℝ)*columnError sec := by sorry

end EFI1PRS.Uniform
