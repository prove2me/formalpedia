-- Prove2me | Theorems.Thm_BSLambda_LLL_intObstruction_two_data
-- name    : BSLambda.LLL.intObstruction_two_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:33.103583+00:00
-- url     : https://prove2.me/theorems/8e485871-8b0a-4004-ad2c-8a697d98bb88
-- title:
--   LLL: int Obstruction two data
-- statement:
--   **Section 9**: every radius-two internal obstruction with owner `h` lies in one of the
--   enumerated branches.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L1002-L1033
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L1002-L1033

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

theorem BSLambda.LLL.intObstruction_two_data [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} (hS : S.card = 9) {h : ι} (hh : h ∈ S) {ω : GateCfg ι r}
    (hobs : IntObstruction Arc 2 S h (toGamma ω)) :
    ∃ (L : Finset ι) (w : (j : ι) → j ∈ L → Fin r) (X : Finset (ι × ι)),
      L ⊆ S.erase h ∧ X ⊆ arcSet Arc (S.erase h) ∧ X.card + L.card = 8 ∧
        ω ∈ branch2 Arc S h L w X := by sorry
