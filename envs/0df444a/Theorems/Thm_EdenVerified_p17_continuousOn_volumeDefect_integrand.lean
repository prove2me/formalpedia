-- Prove2me | Theorems.Thm_EdenVerified_p17_continuousOn_volumeDefect_integrand
-- name    : EdenVerified.p17_continuousOn_volumeDefect_integrand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:56.373389+00:00
-- url     : https://prove2.me/theorems/78541d0e-435b-5f7b-9631-bf346fd4f6ae
-- title:
--   Eden Verified: p17 continuous On volume Defect integrand
-- statement:
--   The Eden Verified construction uses the p17 continuous On volume Defect integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1528-L1532
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1528-L1532

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p17_continuousOn_volumeDefect_integrand :
    ∀ (c : ℝ) (p : PhaseSpace),
    ContinuousOn (fun τ => (radiusSq₁ (evolution c τ p) - 1) ^ 2 +
      (radiusSq₂ (evolution c τ p) - 1) ^ 2) (Set.Ici 0) := by sorry
