-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_psiAP_le_count
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.psiAP_le_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:22.44719+00:00
-- url     : https://prove2.me/theorems/3600e2b0-55ed-4045-a31e-b6963a530c06
-- title:
--   Supply AP: psi AP le count
-- statement:
--   The Supply AP construction uses the psi AP le count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/PsiAPLeCount.lean#L12-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/PsiAPLeCount.lean#L12-L39

import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAP
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_PsiAPLeCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ZeroFreeDirichlet
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP

theorem Formalism.HermitianLattices.Ext.SupplyAP.psiAP_le_count (m a : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    psiAP m a x ≤ Real.log x * ((primesAP m a x).card : ℝ) + 2 * Real.sqrt x * Real.log x := by sorry
