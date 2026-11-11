-- Prove2me | Theorems.Thm_EFI1PRS_Uniform_extraction_hybrid_transition
-- name    : EFI1PRS.Uniform.extraction_hybrid_transition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T05:01:56.565975+00:00
-- url     : https://prove2.me/theorems/1100fbc5-c932-4839-a787-bb4fe215e2bc
-- title:
--   Eq. (5.2) — extraction transition with original quantum past
-- statement:
--   For any amplified EFI pair, construct the actual and witness grouped prefixes $X_i,Z_i$, the public raw-seed extraction channel, and the full hybrids $\mathcal H_i,\mathcal W_i$. There is one threshold valid for every column after which
--
--   $$D\bigl(\operatorname{Ext}_i(Z_i),\mathsf{MM}_{s_iR_i}\otimes(Z_i)_{P_i}\bigr)\le e_\lambda:=2^{-\lambda}+2^{-\lambda^2},$$
--   $$D(\mathcal W_i,\mathcal H_{i-1})\le e_\lambda.$$
--
--   All public seeds and shifts are retained, and extraction leaves the entire original quantum past. The claimed estimates are conclusions of the concrete construction, with no witness or sampler guarantees assumed as extra hypotheses.
--
--   Differences from the source:
--   - encoding: positive unary security parameters and ordinary finite-gate QPT circuits → zero-based wire indices, explicit finite H/S/T/X/Z/CNOT descriptions, coherent workspace and final partial traces; reason: these give explicit circuit semantics and charge all descriptions; the general simulation/compilation bridge remains a proof obligation, not a primitive assumption
--   - encoding: a coherent purification padded to any power-of-two width M at least four, with registers ordered R,F,E,padding → the actual circuit purification, an explicit output/complement wire permutation, and M equal to 2^(Nat.log2(max 4 (2+work))+1); reason: this selects a permitted efficient padding and fixes its wire order; no purification property or entropy estimate is assumed
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, Eq. (5.2), PDF/printed p. 14

import Definitions.Def_EFI1PRS_Uniform_Generator

/-! Rishabh Batra, EFI ⇔ 1PRS, pinned October 2026 STOC submission #273.
Statement-preparation draft; proof is a future solver obligation. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

theorem extraction_hybrid_transition (g : PairPreparation) (hg : IsAmplifiedEFI g) :
    ∃ threshold : ℕ, ∀ sec, threshold ≤ sec → 1 ≤ sec →
      ∀ i, 1 ≤ i → i ≤ windowLength (sourceWidth g sec) →
        distance (seededExtraction (rows (sourceWidth g sec) sec) (retained (sourceWidth g sec) sec) sec
          (columnAndPast g sec i))
          (seededIdeal (rows (sourceWidth g sec) sec) (retained (sourceWidth g sec) sec) sec
            (columnAndPast g sec i)) ≤ columnError sec ∧
        distance (W g sec i) (H g sec (i-1)) ≤ columnError sec := by sorry

end EFI1PRS.Uniform
