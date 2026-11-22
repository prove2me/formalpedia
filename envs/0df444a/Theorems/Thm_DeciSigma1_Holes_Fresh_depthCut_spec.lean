-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_spec
-- name    : DeciSigma1.Holes.Fresh.depthCut_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:00.21364+00:00
-- url     : https://prove2.me/theorems/274ab4e7-bfc9-4b42-8427-e3a394d96ccd
-- title:
--   Fresh: depth Cut spec
-- statement:
--   The depth cuts of an upper occurrence enumerate its lower anchors.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L380-L386
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L380-L386

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}

theorem DeciSigma1.Holes.Fresh.depthCut_spec {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) :
    (∀ d < lowerBlockCount W t o, depthCut W t o d ∈ anchors W t o.1 ∧ o.2.1 < depthCut W t o d ∧
      depthCut W t o d ≤ o.2.2 ∧ anchorCount (anchors W t o.1) (depthCut W t o d) o.2.2 = d) ∧
      depthCut W t o (lowerBlockCount W t o) = o.2.1 := by sorry
