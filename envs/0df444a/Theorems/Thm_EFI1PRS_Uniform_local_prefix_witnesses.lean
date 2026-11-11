-- Prove2me | Theorems.Thm_EFI1PRS_Uniform_local_prefix_witnesses
-- name    : EFI1PRS.Uniform.local_prefix_witnesses
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T05:02:22.991734+00:00
-- url     : https://prove2.me/theorems/fc372493-2997-40bf-8930-dcb2ea49b715
-- title:
--   Lemma 3.1 — local witnesses and their entropy sum
-- statement:
--   For any amplified EFI pair, use the actual ordered pure source, its average $\tau$, and the separately defined witnesses $\gamma_j$. They are uniformly efficiently preparable given the coordinate and satisfy, for every admissible coordinate family,
--
--   $$\gamma_j\approx_c\tau^{[j]},\qquad\operatorname{Tr}_{Q_j}\gamma_j=\tau^{[j-1]},\qquad\sum_{j=1}^{M}h_j=1+\chi\ge2-\eta(\lambda).$$
--
--   Here $h_j=H(Q_j\mid Q_{<j})_{\gamma_j}$ may be negative. The witnesses need not be marginals of one common global state; the exact preceding marginal is retained.
--
--   Differences from the source:
--   - encoding: for every growing prefix or column index → quantification over every admissible security-parameter-dependent index sequence; reason: non-uniform tests may hard-wire a different index at each parameter; no index computability is added
--   - encoding: positive unary security parameters and ordinary finite-gate QPT circuits → zero-based wire indices, explicit finite H/S/T/X/Z/CNOT descriptions, coherent workspace and final partial traces; reason: these give explicit circuit semantics and charge all descriptions; the general simulation/compilation bridge remains a proof obligation, not a primitive assumption
--   - encoding: a coherent purification padded to any power-of-two width M at least four, with registers ordered R,F,E,padding → the actual circuit purification, an explicit output/complement wire permutation, and M equal to 2^(Nat.log2(max 4 (2+work))+1); reason: this selects a permitted efficient padding and fixes its wire order; no purification property or entropy estimate is assumed
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, Lemma 3.1, PDF/printed p. 11

import Definitions.Def_EFI1PRS_Uniform_Generator

/-! Rishabh Batra, EFI ⇔ 1PRS, pinned October 2026 STOC submission #273.
Statement-preparation draft; proof is a future solver obligation. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

theorem local_prefix_witnesses (g : PairPreparation) (hg : IsAmplifiedEFI g) :
    IndexedEfficient (sourceWidth g) (fun _ j => j) (gamma g) ∧
    (∀ index : ℕ → ℕ, (∀ sec, 1 ≤ sec → 1 ≤ index sec ∧ index sec ≤ sourceWidth g sec) →
      ComputationallyIndistinguishable (fun sec => gamma g sec (index sec))
        (fun sec => prefixState (tau g sec) (index sec))) ∧
    (∀ sec j, 1 ≤ sec → 1 ≤ j → j ≤ sourceWidth g sec →
      prefixState (gamma g sec j) (j-1) = prefixState (tau g sec) (j-1)) ∧
    ∀ sec, 1 ≤ sec →
      (∑ j ∈ Finset.range (sourceWidth g sec), localEntropy g sec (j+1)) = 1 + chi g sec ∧
      2 - eta g sec ≤ 1 + chi g sec := by sorry

end EFI1PRS.Uniform
