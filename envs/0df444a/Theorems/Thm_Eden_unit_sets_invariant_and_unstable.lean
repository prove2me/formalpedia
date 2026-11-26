-- Prove2me | Theorems.Thm_Eden_unit_sets_invariant_and_unstable
-- name    : Eden.unit_sets_invariant_and_unstable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:01:32.416625+00:00
-- url     : https://prove2.me/theorems/250c78b1-4696-411b-8ce5-190be6e61ea1
-- title:
--   Eden: unit sets invariant and unstable
-- statement:
--   All three invariant sets are strictly invariant and unstable relative to A.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NonlinearInstability.lean#L154-L168
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NonlinearInstability.lean#L154-L168

import Definitions.Def_Eden_InstabilityGeometry
import Definitions.Def_Eden_NonlinearInstability
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.unit_sets_invariant_and_unstable (c : ℝ)
    {K : Set PhaseSpace} (hK : K = firstCircle 1 ∨ K = secondCircle 1 ∨ K = torus) :
    (∀ t : ℝ, 0 ≤ t → evolution c t '' K = K) ∧
      UnstableRelativeTo c attractor K ∧ UnstableRelativeTo c univ K := by sorry
