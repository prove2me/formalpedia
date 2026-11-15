-- Prove2me | Theorems.Thm_APFPaper5_K3_euler_core
-- name    : APFPaper5.K3.euler_core
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:50:17.50237+00:00
-- url     : https://prove2.me/theorems/12a1cdfa-9102-4b85-8d4b-e23aa19d2644
-- title:
--   Euler core
-- statement:
--   Supporting result: euler core. It holds for exactly the parameters and hypotheses displayed in the attached formal statement. Commuting real-linear maps are real combinations of eight explicit generated maps. With hroot, commuting cost-preserving maps factor into four generator actions; unseen linear isometries are generated or flipped-generated. Squares and explicit admitted-half assumptions give further consequences. This classifies model endomorphisms. It does not identify the physical represented observable algebra or prove its J-module closure, faithful action, classification import, or actual generator admission. Keep hroot wherever bound.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1862-1888,2006-2044'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_generator_completeness.lean', 'sha256': '72583ee936562d54c86c90f3789e818a94941ead02b97379070210cffa87cab0', 'line': 58, 'declaration': 'APFPaper5.K3.euler_core'}]

import Definitions.Def_APFPaper5_K3_HeldMaps
import Definitions.Def_APFPaper5_K3_TwoPoint
import Theorems.Thm_APFPaper5_K3_built_commutes_common
import Theorems.Thm_APFPaper5_K3_built_commutes_quarter
import Theorems.Thm_APFPaper5_K3_comp_additiveHomogeneous
import Theorems.Thm_APFPaper5_K3_built_additiveHomogeneous
import Theorems.Thm_APFPaper5_K3_built_preserves_totalCost
import Theorems.Thm_APFPaper5_K3_built_unseen
import Theorems.Thm_APFPaper5_K3_onePlaneQuarter_not_built
import Theorems.Thm_APFPaper5_K3_rateFlip_additiveHomogeneous
import Theorems.Thm_APFPaper5_K3_rateFlip_preserves_totalCost
import Theorems.Thm_APFPaper5_K3_rateFlip_not_built
import Theorems.Thm_APFPaper5_K3_rateFlip_comp_commutes
import Theorems.Thm_APFPaper5_K3_rateFlip_rateFlip
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.euler_core (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t)
    (p1 p2 p3 p4 q1 q2 q3 q4 : ℝ)
    (hN1 : p1 * p1 + p2 * p2 + p3 * p3 + p4 * p4 = 1)
    (hN2 : q1 * q1 + q2 * q2 + q3 * q3 + q4 * q4 = 1)
    (hO1 : p1 * q1 + p2 * q2 + p3 * q3 + p4 * q4 = 0)
    (hO2 : p2 * q1 - p1 * q2 + p4 * q3 - p3 * q4 = 0) :
    ∃ c0 s0 c1 s1 c2 s2 c3 s3 : ℝ, c0 * c0 + s0 * s0 = 1 ∧ c1 * c1 + s1 * s1 = 1 ∧
      c2 * c2 + s2 * s2 = 1 ∧ c3 * c3 + s3 * s3 = 1 ∧
      ∀ h : Held2,
        (⟨h.a1 * p1 - h.a2 * p2 + h.b1 * q1 - h.b2 * q2, h.a1 * p2 + h.a2 * p1 + h.b1 * q2 + h.b2 * q1,
          h.a1 * p3 - h.a2 * p4 + h.b1 * q3 - h.b2 * q4,
          h.a1 * p4 + h.a2 * p3 + h.b1 * q4 + h.b2 * q3⟩ : Held2) =
        commonTurn c0 s0 (relativeTurn c1 s1 (mix c2 s2 (relativeTurn c3 s3 h))) := by sorry
