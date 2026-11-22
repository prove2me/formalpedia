-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_channel_iff_events
-- name    : DeciSigma1.Full.Reduction.channel_iff_events
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:16:52.987453+00:00
-- url     : https://prove2.me/theorems/efbae228-9c57-4709-87d4-b631642d2b81
-- title:
--   Reduction: channel iff events
-- statement:
--   The channel from coordinate `i` to coordinate `j` carries an admitted pair exactly when the
--   seed of `j` derives the exclusion of `i` or the opposite sign of the seed of `i`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L223-L258
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Compile.lean#L223-L258

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

theorem DeciSigma1.Full.Reduction.channel_iff_events {W : Fin k → List (Fin n)} (i j : Fin k)
    (hi : (compile c Γ q m).Eligible W i) (hj : (compile c Γ q m).Eligible W j) :
    (∃ pq ∈ (compile c Γ q m).channel W i j, (compile c Γ q m).admitted pq.1 pq.2 = true) ↔
      Event c Γ (seed (q j) (m j) (W j)) (exclusion (q i) (m i) (W i)) ∨
      Event c Γ (seed (q j) (m j) (W j)) (flipC (seed (q i) (m i) (W i))) := by sorry
