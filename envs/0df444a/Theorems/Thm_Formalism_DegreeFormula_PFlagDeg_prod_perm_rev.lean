-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PFlagDeg_prod_perm_rev
-- name    : Formalism.DegreeFormula.PFlagDeg.prod_perm_rev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:32.154379+00:00
-- url     : https://prove2.me/theorems/a8250f4a-5ea6-489a-9f59-8dd0b6e8ffab
-- title:
--   PFlag Deg: prod perm rev
-- statement:
--   The PFlag Deg construction uses the prod perm rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L12-L18

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

theorem Formalism.DegreeFormula.PFlagDeg.prod_perm_rev {M : Type*} [CommMonoid M] {N : ℕ} (s : Equiv.Perm (Fin N)) (g : ℕ → M) :
    ∏ i : Fin N, g (N - 1 - ((s i : Fin N) : ℕ)) = ∏ i : Fin N, g (i : ℕ) := by sorry
