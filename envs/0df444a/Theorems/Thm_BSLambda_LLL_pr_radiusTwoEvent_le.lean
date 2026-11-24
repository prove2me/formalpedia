-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_radiusTwoEvent_le
-- name    : BSLambda.LLL.pr_radiusTwoEvent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:46.748327+00:00
-- url     : https://prove2.me/theorems/1e71d66a-09f1-443e-baf7-4a428acd73f4
-- title:
--   LLL: pr radius Two Event le
-- statement:
--   **Section 9**: the consolidated radius-two obstruction on a nine-element support has
--   probability at most `radiusTwoConst / r ^ 20`.  Each non-owner has one residual discrepancy;
--   if `l` of them spend it on a discretionary zero there are at most `C(8,l) r ^ l` choices, at
--   most `C(28, 8-l)` choices of an exceptional superset of the missing arcs, and each of the
--   remaining `20 + l` arc labels must hit a target set of size at most two.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L1177-L1195
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L1177-L1195

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

theorem BSLambda.LLL.pr_radiusTwoEvent_le [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} (hS : S.card = 9) :
    pr (β := fun _ : ι × ι => Fin r) (radiusTwoEvent Arc S)
      ≤ (radiusTwoConst : ℝ) / (r : ℝ) ^ 20 := by sorry
