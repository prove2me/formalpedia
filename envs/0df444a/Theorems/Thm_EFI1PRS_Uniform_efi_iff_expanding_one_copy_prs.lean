-- Prove2me | Theorems.Thm_EFI1PRS_Uniform_efi_iff_expanding_one_copy_prs
-- name    : EFI1PRS.Uniform.efi_iff_expanding_one_copy_prs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T05:03:29.200551+00:00
-- url     : https://prove2.me/theorems/af8ab031-a873-4b6d-b318-c96da70829c8
-- title:
--   Theorem 5.1 — EFI pairs exist if and only if expanding 1PRS exist
-- statement:
--   An efficiently generated far-indistinguishable pair is a single uniform QPT branch preparation with computationally indistinguishable outputs at eventual inverse-polynomial trace distance. An expanding single-copy pseudorandom generator is one uniform QPT algorithm mapping every fixed hidden $r(\lambda)$-bit key to a normalized pure $n(\lambda)$-qubit state, with $n(\lambda)>r(\lambda)$ at every positive security parameter, whose key average is computationally indistinguishable from the maximally mixed state. Then
--
--   $$\bigl(\text{EFI pairs exist}\bigr)\quad\Longleftrightarrow\quad\bigl(\text{expanding single-copy pseudorandom state generators exist}\bigr).$$
--
--   Both sides quantify over honest generators without advice. Security on both sides covers all non-uniform polynomial-size quantum circuits with arbitrary polynomial-qubit mixed advice independent of the fresh challenge and key. The theorem has no premise supplying witnesses, extraction, amplification, security reductions or a generator for either side.
--
--   Differences from the source:
--   - encoding: positive unary security parameters and ordinary finite-gate QPT circuits → zero-based wire indices, explicit finite H/S/T/X/Z/CNOT descriptions, coherent workspace and final partial traces; reason: these give explicit circuit semantics and charge all descriptions; the general simulation/compilation bridge remains a proof obligation, not a primitive assumption
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, Theorem 5.1, PDF/printed p. 13

import Definitions.Def_EFI1PRS_Uniform_Generator

/-! Rishabh Batra, EFI ⇔ 1PRS, pinned October 2026 STOC submission #273.
Statement-preparation draft; proof is a future solver obligation. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

theorem efi_iff_expanding_one_copy_prs :
    (∃ g : PairPreparation, IsEFI g) ↔
      (∃ g : KeyedPreparation, IsExpandingOneCopyPRS g) := by sorry

end EFI1PRS.Uniform
