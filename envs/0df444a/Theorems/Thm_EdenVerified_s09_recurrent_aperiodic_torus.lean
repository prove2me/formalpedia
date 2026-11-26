-- Prove2me | Theorems.Thm_EdenVerified_s09_recurrent_aperiodic_torus
-- name    : EdenVerified.s09_recurrent_aperiodic_torus
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:24:11.278798+00:00
-- url     : https://prove2.me/theorems/fb091a79-57aa-536d-98f0-fccce6789e78
-- title:
--   Eden Verified: s09 recurrent aperiodic torus
-- statement:
--   Every point is recurrent in the torus topology, and no point is periodic.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L302-L307
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L302-L307

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s09_recurrent_aperiodic_torus (c : ℝ) (p : torus) :
    (∀ U : Set torus, U ∈ 𝓝 p → ∀ R : ℝ, 0 < R →
      ∃ t : ℝ, R < t ∧ torusEvolution c t p ∈ U) ∧
    (∀ t : ℝ, 0 < t → torusEvolution c t p ≠ p) := by sorry
