-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_endpoint_neg_of_extended_cut
-- name    : DeciSigma1.Full.Reduction.endpoint_neg_of_extended_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:10:26.011798+00:00
-- url     : https://prove2.me/theorems/6c162fec-79f1-448e-ab06-761f7e49a478
-- title:
--   Reduction: endpoint neg of extended cut
-- statement:
--   If the upper run of `p` along `w ++ z` is nonempty at a cut beyond `w`, the upper run on `w`
--   meets the signed variables below a negative fact.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L156-L163
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L156-L163

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Reduction.endpoint_neg_of_extended_cut {p : V × Bool} {w z : List (Fin n)} {e : Nat}
    (he : e ≤ (w ++ z).length) (hlt : w.length < e)
    (hp : (Automata.upperRun (signed c Γ) p ((w ++ z).take e)).Nonempty) :
    (Automata.upperRun (signed c Γ) p w ∩ forbiddenPredecessors c Γ).Nonempty := by sorry
