-- Prove2me | Theorems.Thm_EdenVerified_s02_common_index_dimension
-- name    : EdenVerified.s02_common_index_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:21:44.5843+00:00
-- url     : https://prove2.me/theorems/6a9ece59-997b-5cfd-96ad-c4f1a84222b2
-- title:
--   Eden Verified: s02 common index dimension
-- statement:
--   The common-index dimension and its maximising torus.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L172-L180
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L172-L180

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s02_common_index_dimension (c : ℝ) (hc : 4 < c) :
    (∀ p : PhaseSpace, commonIndexLocalDimension c p =
      4 + spectrumPartialSum (lyapunovExponent c p) 4 / c) ∧
    commonIndexDimension c = 4 + 4/c ∧
    IsGreatest (commonIndexLocalDimension c '' attractor) (4 + 4/c) ∧
    (∀ p ∈ attractor, commonIndexLocalDimension c p = 4 + 4/c ↔ p ∈ torus) := by sorry
