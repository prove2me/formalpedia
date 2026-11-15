-- Prove2me | Theorems.Thm_APFPaper5_K3_retracing_orbit_same_now_different_later
-- name    : APFPaper5.K3.retracing_orbit_same_now_different_later
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:01:50.941423+00:00
-- url     : https://prove2.me/theorems/11d6abec-9213-4c99-a85b-494cb85a4db9
-- title:
--   Retracing orbit same now different later
-- statement:
--   For a two-sided orbit whose present readings agree at opposite indices, if the readings one step before and after n differ, the states at n and minus n have equal present readings but different readings after one step. Strict order preservation is a substantive hypothesis, not a consequence of smoothness in these theorems. Recurrence, retracing and change are supplied; no physical rate is derived.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1650'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_number_alone_cannot_return.lean', 'sha256': '65e45c5ff991b83e9e257c2ef097ddee683754d4dffcae8d314b06443fa3bd17', 'line': 82, 'declaration': 'APFPaper5.K3.retracing_orbit_same_now_different_later'}]

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.retracing_orbit_same_now_different_later {X R : Type*} (now : X → R) (D : X → X)
    (o : ℤ → X) (ho : ∀ n : ℤ, o (n + 1) = D (o n)) (hret : ∀ n : ℤ, now (o (-n)) = now (o n))
    (n : ℤ) (hmove : now (o (n - 1)) ≠ now (o (n + 1))) :
    now (o (-n)) = now (o n) ∧ now (D (o (-n))) ≠ now (D (o n)) := by sorry
