-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PFlagDeg_vandermonde_sum
-- name    : Formalism.DegreeFormula.PFlagDeg.vandermonde_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:08.264219+00:00
-- url     : https://prove2.me/theorems/1a182e39-802c-4e00-b7f1-ec7e6f29a794
-- title:
--   PFlag Deg: vandermonde sum
-- statement:
--   The PFlag Deg construction uses the vandermonde sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L122-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L122-L136

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

theorem Formalism.DegreeFormula.PFlagDeg.vandermonde_sum {N : ℕ} (v : Fin N → ℝ) :
    ∑ s : Equiv.Perm (Fin N), ((Equiv.Perm.sign s : ℤ) : ℝ) *
        ∏ i, v i ^ (N - 1 - ((s i : Fin N) : ℕ)) =
      ∏ i : Fin N, ∏ k : Fin N, if i < k then v i - v k else 1 := by sorry
