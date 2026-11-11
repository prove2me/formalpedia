-- Prove2me | Theorems.Thm_EFI1PRS_Uniform_column_min_entropy
-- name    : EFI1PRS.Uniform.column_min_entropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T05:03:39.542197+00:00
-- url     : https://prove2.me/theorems/598b4a3d-870a-4287-b44c-f55a217814f7
-- title:
--   Lemma 4.2 — column smooth min-entropy and margin
-- statement:
--   For any amplified EFI pair, take the source's exact integral $M,L,N,t,\ell$ and independent-row column witnesses. Set $\epsilon=2^{-\lambda}/12$ and $k=7t/(4M)$. There is one threshold, independent of the column, after which every $i\in[N(\lambda)]$ satisfies
--
--   $$H_{\min}^{\epsilon}(C_i\mid P_i)_{\Omega_i^{\otimes t}}\ge k,\qquad\frac{t+k}{2}-\ell=\frac{t}{8M}\ge\lambda.$$
--
--   The past is the original quantum register $P_i=(J^t,C_1,\ldots,C_{i-1})$, under the explicit row-to-column permutation. In particular $t=2^{16}M^2(\lambda+4)$, with no rounded extraction length.
--
--   Differences from the source:
--   - encoding: a supremum of domination exponents, with purified-distance smoothing → EReal suprema, trace-one reference states and the full published subnormalized purified-distance ball; reason: infinite entropy is represented without a junk real supremum or a support restriction
--   - encoding: positive unary security parameters and ordinary finite-gate QPT circuits → zero-based wire indices, explicit finite H/S/T/X/Z/CNOT descriptions, coherent workspace and final partial traces; reason: these give explicit circuit semantics and charge all descriptions; the general simulation/compilation bridge remains a proof obligation, not a primitive assumption
--   - encoding: a coherent purification padded to any power-of-two width M at least four, with registers ordered R,F,E,padding → the actual circuit purification, an explicit output/complement wire permutation, and M equal to 2^(Nat.log2(max 4 (2+work))+1); reason: this selects a permitted efficient padding and fixes its wire order; no purification property or entropy estimate is assumed
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, Lemma 4.2, PDF/printed p. 12

import Definitions.Def_EFI1PRS_Uniform_Generator

/-! Rishabh Batra, EFI ⇔ 1PRS, pinned October 2026 STOC submission #273.
Statement-preparation draft; proof is a future solver obligation. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

theorem column_min_entropy (g : PairPreparation) (hg : IsAmplifiedEFI g) :
    ∃ threshold : ℕ, ∀ sec, threshold ≤ sec → 1 ≤ sec →
      ∀ i, 1 ≤ i → i ≤ windowLength (sourceWidth g sec) →
      let M := sourceWidth g sec
      let t := (rows M sec : ℝ)
      let k := 7*t/(4*(M : ℝ))
      (k : EReal) ≤ smoothConditionalMin (columnAndPast g sec i) ((2 : ℝ)^(-(sec : ℤ))/12) ∧
      (t+k)/2-(retained M sec : ℝ) = t/(8*(M : ℝ)) ∧
      (sec : ℝ) ≤ t/(8*(M : ℝ)) := by sorry

end EFI1PRS.Uniform
