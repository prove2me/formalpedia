-- Prove2me | Theorems.Thm_EFI1PRS_Uniform_efi_amplification
-- name    : EFI1PRS.Uniform.efi_amplification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T05:02:56.861421+00:00
-- url     : https://prove2.me/theorems/e8a790e5-3202-42bc-8cb6-98264637c769
-- title:
--   Fact 2.7 — EFI amplification
-- statement:
--   EFI existence is unchanged by amplification. Both sides use one uniform generator, computational hiding against every non-uniform polynomial-size quantum-advice test, and the source's ordinary circuit model. Then
--
--   $$(\exists\text{ EFI pair with eventual inverse-polynomial distance})\quad\Longleftrightarrow\quad(\exists\text{ EFI pair with distance }1-\operatorname{negl}(\lambda)).$$
--
--   The amplified pair may differ from the original one. This is the bridge from Definition 2.6 to the amplified setting used throughout the construction.
--
--   Differences from the source:
--   - reading: the EFI definition is unchanged if the distance requirement is replaced → equivalence of existence of original and amplified pairs, allowing the pair to change; reason: a particular inverse-polynomial pair need not already have near-unit distance
--   - encoding: positive unary security parameters and ordinary finite-gate QPT circuits → zero-based wire indices, explicit finite H/S/T/X/Z/CNOT descriptions, coherent workspace and final partial traces; reason: these give explicit circuit semantics and charge all descriptions; the general simulation/compilation bridge remains a proof obligation, not a primitive assumption
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, Fact 2.7, PDF/printed p. 8

import Definitions.Def_EFI1PRS_Uniform_Generator

/-! Rishabh Batra, EFI ⇔ 1PRS, pinned October 2026 STOC submission #273.
Statement-preparation draft; proof is a future solver obligation. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

theorem efi_amplification :
    (∃ g : PairPreparation, IsEFI g) ↔
      (∃ g : PairPreparation, IsAmplifiedEFI g) := by sorry

end EFI1PRS.Uniform
