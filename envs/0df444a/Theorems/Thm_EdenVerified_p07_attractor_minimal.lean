-- Prove2me | Theorems.Thm_EdenVerified_p07_attractor_minimal
-- name    : EdenVerified.p07_attractor_minimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:32:35.387798+00:00
-- url     : https://prove2.me/theorems/4c5eacf7-0c17-46cb-898c-3c2f1f291f19
-- title:
--   Eden Verified: p07 attractor minimal
-- statement:
--   The Eden Verified construction uses the p07 attractor minimal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L932-L936
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L932-L936

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p07_attractor_minimal :
    ∀ {c : ℝ} {C : Set PhaseSpace} (hcompact : IsCompact C)
    (hC : UniformlyAttractsBounded c C),
    attractor ⊆ C := by sorry
