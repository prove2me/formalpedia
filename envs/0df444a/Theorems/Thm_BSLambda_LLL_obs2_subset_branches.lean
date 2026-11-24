-- Prove2me | Theorems.Thm_BSLambda_LLL_obs2_subset_branches
-- name    : BSLambda.LLL.obs2_subset_branches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:43.622267+00:00
-- url     : https://prove2.me/theorems/45e383bf-2ada-4d09-bea2-c72a82fa3bc3
-- title:
--   LLL: obs2 subset branches
-- statement:
--   **Section 9**: the radius-two event for a fixed owner is covered by the branches.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L1037-L1050
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L1037-L1050

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
open scoped Classical

theorem BSLambda.LLL.obs2_subset_branches [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} (hS : S.card = 9)
    {h : ι} (hh : h ∈ S) :
    (Finset.univ.filter fun ω : GateCfg ι r => IntObstruction Arc 2 S h (toGamma ω)) ⊆
      (S.erase h).powerset.biUnion fun L =>
        (L.pi fun _ => (Finset.univ : Finset (Fin r))).biUnion fun w =>
          ((arcSet Arc (S.erase h)).powersetCard (8 - L.card)).biUnion fun X =>
            branch2 Arc S h L w X := by sorry
