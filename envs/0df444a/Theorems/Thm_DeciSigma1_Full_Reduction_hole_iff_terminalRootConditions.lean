-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_hole_iff_terminalRootConditions
-- name    : DeciSigma1.Full.Reduction.hole_iff_terminalRootConditions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:17:21.037795+00:00
-- url     : https://prove2.me/theorems/6e4a3b25-873c-45c2-9341-dd8a7f136707
-- title:
--   Reduction: hole iff terminal Root Conditions
-- statement:
--   A tuple is a hole of the reader of mode `m` exactly when its seeds and exclusions satisfy
--   `TerminalRootConditions`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L262-L285
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L262-L285

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Constraints DeciSigma1.Full.Closure DeciSigma1.Readers.Table
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
  {q : Fin k → V × V} {m : Fin k → Bool}

theorem DeciSigma1.Full.Reduction.hole_iff_terminalRootConditions (m : Fin k → Bool) (W : Fin k → List (Fin n)) :
    (compile c Γ q m).IsHole W ↔ TerminalRootConditions c Γ
      (fun i => seed (q i) (m i) (W i))
      (fun i => exclusion (q i) (m i) (W i)) := by sorry
