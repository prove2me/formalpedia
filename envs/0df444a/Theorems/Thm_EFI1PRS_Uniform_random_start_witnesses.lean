-- Prove2me | Theorems.Thm_EFI1PRS_Uniform_random_start_witnesses
-- name    : EFI1PRS.Uniform.random_start_witnesses
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T05:02:26.787598+00:00
-- url     : https://prove2.me/theorems/622af7a9-39bb-4f30-9bd4-4119d534b1f9
-- title:
--   Lemma 4.1 — random-start quantum witnesses
-- statement:
--   For an arbitrary amplified EFI pair and the actual random-start row construction, every witness $\Omega_i$ is uniformly efficiently preparable given its column index. For every admissible index family, and every $1\le i\le N$ at each positive security parameter,
--
--   $$\operatorname{Tr}_{A_i}\Omega_i=\omega_{i-1},\qquad\Omega_i\approx_c\omega_i,$$
--   $$H(A_i\mid J,A_{<i})_{\Omega_i}\ge\frac1M\sum_{j=1}^{M}h_j\ge\frac{2-\eta}{M}.$$
--
--   The public shift remains part of the conditioning system. The first truncated copy and all actual preceding-copy factors are included in the specified witness.
--
--   Differences from the source:
--   - encoding: for every growing prefix or column index → quantification over every admissible security-parameter-dependent index sequence; reason: non-uniform tests may hard-wire a different index at each parameter; no index computability is added
--   - encoding: positive unary security parameters and ordinary finite-gate QPT circuits → zero-based wire indices, explicit finite H/S/T/X/Z/CNOT descriptions, coherent workspace and final partial traces; reason: these give explicit circuit semantics and charge all descriptions; the general simulation/compilation bridge remains a proof obligation, not a primitive assumption
--   - encoding: a coherent purification padded to any power-of-two width M at least four, with registers ordered R,F,E,padding → the actual circuit purification, an explicit output/complement wire permutation, and M equal to 2^(Nat.log2(max 4 (2+work))+1); reason: this selects a permitted efficient padding and fixes its wire order; no purification property or entropy estimate is assumed
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, Lemma 4.1, PDF/printed p. 12

import Definitions.Def_EFI1PRS_Uniform_Generator

/-! Rishabh Batra, EFI ⇔ 1PRS, pinned October 2026 STOC submission #273.
Statement-preparation draft; proof is a future solver obligation. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

theorem random_start_witnesses (g : PairPreparation) (hg : IsAmplifiedEFI g) :
    IndexedEfficient (fun sec => windowLength (sourceWidth g sec))
      (fun sec i => shiftBits (sourceWidth g sec)+i) (bigOmega g) ∧
    (∀ index : ℕ → ℕ,
      (∀ sec, 1 ≤ sec → 1 ≤ index sec ∧ index sec ≤ windowLength (sourceWidth g sec)) →
      ComputationallyIndistinguishable (fun sec => bigOmega g sec (index sec))
        (fun sec => omega g sec (index sec))) ∧
    ∀ sec i, 1 ≤ sec → 1 ≤ i → i ≤ windowLength (sourceWidth g sec) →
      prefixState (bigOmega g sec i) (shiftBits (sourceWidth g sec)+(i-1)) = omega g sec (i-1) ∧
      ((∑ j ∈ Finset.range (sourceWidth g sec), localEntropy g sec (j+1)) /
        (sourceWidth g sec : ℝ) ≤ conditionalEntropy
          (lastQubitPast (shiftBits (sourceWidth g sec)) i (bigOmega g sec i))) ∧
      ((2-eta g sec)/(sourceWidth g sec : ℝ) ≤
        (∑ j ∈ Finset.range (sourceWidth g sec), localEntropy g sec (j+1)) /
          (sourceWidth g sec : ℝ)) := by sorry

end EFI1PRS.Uniform
