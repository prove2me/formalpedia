-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PFlagDeg_linRoot_eq
-- name    : Formalism.DegreeFormula.PFlagDeg.linRoot_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:29.025253+00:00
-- url     : https://prove2.me/theorems/00510775-3ec0-4d3a-9e0d-2039755f2c70
-- title:
--   PFlag Deg: lin Root eq
-- statement:
--   The PFlag Deg construction uses the lin Root eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L39-L44

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

theorem Formalism.DegreeFormula.PFlagDeg.linRoot_eq {ι : Type} [Fintype ι] {N : ℕ} (lam : ι → Fin N → ℝ) :
    linRoot lam = ∑ x : ι × Fin N, (-lam x.1 x.2) • (X x : MvPolynomial (ι × Fin N) ℝ) := by sorry
