-- Prove2me | Theorems.Thm_BSLambda_LLL_exists_active_flag_of_intObstruction
-- name    : BSLambda.LLL.exists_active_flag_of_intObstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:06.369749+00:00
-- url     : https://prove2.me/theorems/542ce51c-d1ec-4614-a841-e3351fe2589b
-- title:
--   LLL: exists active flag of int Obstruction
-- statement:
--   **Section 8**: on a five-element support a radius-one internal obstruction forces one
--   of the two patterns.  If `h → j` then `|Z j| = 1` and `j` can have no internal miss; if
--   `j → h` then the arc `j → h` is automatically a miss, so `Z j = ∅` and again `j` has no
--   other miss.  Hence any two vertices beating `h` would give one of them a second miss, so at
--   most one vertex beats `h`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L752-L763
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L752-L763

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι]

theorem BSLambda.LLL.exists_active_flag_of_intObstruction {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {γ : ι → ι → Fin r} {S : Finset ι} (hS : S.card = 5) {h : ι} (hh : h ∈ S)
    (hobs : IntObstruction Arc 1 S h γ) :
    ∃ F : Flag1 ι, F.Active Arc ∧ F.supp = S ∧ F.owner = h ∧
      ∀ p ∈ arcSet Arc F.nonOwners, γ p.1 p.2 = γ h p.2 := by sorry
