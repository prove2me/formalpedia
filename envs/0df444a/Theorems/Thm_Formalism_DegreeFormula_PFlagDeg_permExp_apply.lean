-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PFlagDeg_permExp_apply
-- name    : Formalism.DegreeFormula.PFlagDeg.permExp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:23.249907+00:00
-- url     : https://prove2.me/theorems/3f16ccf3-de1f-4e62-9a9f-8ca135e645d1
-- title:
--   PFlag Deg: perm Exp apply
-- statement:
--   The PFlag Deg construction uses the perm Exp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L27-L29

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_FlagDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.DegreeFormula
open Formalism.DegreeFormula.PFlagDeg

theorem Formalism.DegreeFormula.PFlagDeg.permExp_apply {ι : Type} [Fintype ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) (x : ι × Fin N) :
    permExp σ x = N - 1 - ((σ x.1 x.2 : Fin N) : ℕ) := by sorry
