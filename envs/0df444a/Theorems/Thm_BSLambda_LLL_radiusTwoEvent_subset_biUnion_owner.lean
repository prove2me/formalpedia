-- Prove2me | Theorems.Thm_BSLambda_LLL_radiusTwoEvent_subset_biUnion_owner
-- name    : BSLambda.LLL.radiusTwoEvent_subset_biUnion_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:30.430211+00:00
-- url     : https://prove2.me/theorems/cab021b0-1343-474e-bf58-c330ed36440f
-- title:
--   LLL: radius Two Event subset bi Union owner
-- statement:
--   **Section 9**: the consolidated event is the union over the nine possible owners.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L897-L903
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L897-L903

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

theorem BSLambda.LLL.radiusTwoEvent_subset_biUnion_owner (Arc : ι → ι → Bool) (S : Finset ι) :
    radiusTwoEvent (r := r) Arc S ⊆ S.biUnion fun h =>
      Finset.univ.filter fun ω : GateCfg ι r => IntObstruction Arc 2 S h (toGamma ω) := by sorry
