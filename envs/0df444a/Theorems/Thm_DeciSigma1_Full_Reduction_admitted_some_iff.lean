-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_admitted_some_iff
-- name    : DeciSigma1.Full.Reduction.admitted_some_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:17:02.875312+00:00
-- url     : https://prove2.me/theorems/45ac2a2f-fce2-46fb-922b-820fac0a767e
-- title:
--   Reduction: admitted some iff
-- statement:
--   The Reduction construction uses the admitted some iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L215-L219
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L215-L219

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
public import Theorems.Thm_DeciSigma1_Constraints_UpperAt_map

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Constraints DeciSigma1.Full.Closure DeciSigma1.Readers.Table
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
  {q : Fin k → V × V} {m : Fin k → Bool}
omit [Fintype V]

theorem DeciSigma1.Full.Reduction.admitted_some_iff (Ph Qh Pt Qt : Finset (V × Bool)) :
    Compile.admitted (some (Ph, Qh)) (some (Pt, Qt)) = true ↔
      (Pt ∩ Qh).Nonempty ∨ (Pt ∩ Ph.map flipEmb).Nonempty := by sorry
