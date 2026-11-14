-- Prove2me | Theorems.Thm_APFPaper5_K3_exists_amplitude_of_rotation
-- name    : APFPaper5.K3.exists_amplitude_of_rotation
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:21:49.547874+00:00
-- url     : https://prove2.me/theorems/be3832f3-cd02-4684-afe1-348883caa9ef
-- title:
--   Every unit real pair has a unit-pair square root under explicit real-root existence
-- statement:
--   Assume hroot: every nonnegative real number has a nonnegative real square root. For real x and y satisfying x²+y²=1, there exists a real pair p of unit length with double p=(x,y). The square-root existence premise remains explicit in the formal statement. This theorem proves existence only; uniqueness up to sign and identification with physical amplitudes are not established by this declaration. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1686-1717'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_amplitude_plane.lean', 'line': 51, 'declaration': 'APFPaper5.K3.exists_amplitude_of_rotation', 'sha256': '6f177e4fc6d13f2cdd6af524288164da48f11668883a514d4ef443a76f8c7a94'}]

import Definitions.Def_APFPaper5_K3_AmplitudePair
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.exists_amplitude_of_rotation
    (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t)
    (x y : ℝ) (hxy : x * x + y * y = 1) :
    ∃ p : ℝ × ℝ, p.1 * p.1 + p.2 * p.2 = 1 ∧ double p = (x, y) := by sorry
