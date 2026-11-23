-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_rowGen_lpMinor
-- name    : Formalism.GradedWeylDivisibility.rowGen_lpMinor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:23.399577+00:00
-- url     : https://prove2.me/theorems/000fb1d3-d3f2-4d02-a48e-dafb2ac15d2e
-- title:
--   Graded Weyl Divisibility: row Gen lp Minor
-- statement:
--   The Graded Weyl Divisibility construction uses the row Gen lp Minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/HWRaise.lean#L15-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/HWRaise.lean#L15-L60

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRaise
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.rowGen_lpMinor (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (hab : a < b)
    (m : ℕ) (hr : m ≤ r) (hn : m ≤ n) :
    rowGen R a b (lpMinor R m hr hn) = Polynomial.C (lpMinor R m hr hn) := by sorry
