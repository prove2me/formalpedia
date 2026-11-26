-- Prove2me | Theorems.Thm_EdenVerified_s02_index_and_sums
-- name    : EdenVerified.s02_index_and_sums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:21:04.397298+00:00
-- url     : https://prove2.me/theorems/f281093d-33b2-5eb7-b297-a806e0e26095
-- title:
--   Eden Verified: s02 index and sums
-- statement:
--   The least global index and the corresponding attained exponent sums.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L162-L169
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L162-L169

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s02_index_and_sums (c : ℝ) (hc : 4 < c) :
    IsLeast (commonIndexCandidates c) 4 ∧ commonIndex c = 4 ∧
    (∀ p : PhaseSpace, lyapunovExponent c p 4 = -c) ∧
    IsGreatest ((fun p => spectrumPartialSum (lyapunovExponent c p) 4) '' attractor) 4 ∧
    IsGreatest ((fun p => spectrumPartialSum (lyapunovExponent c p) 5) '' attractor) (4-c) ∧
    4-c < 0 := by sorry
