-- Prove2me | Theorems.Thm_EdenVerified_p06_radiusEvolution_antitoneOn
-- name    : EdenVerified.p06_radiusEvolution_antitoneOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:31:35.772124+00:00
-- url     : https://prove2.me/theorems/1c92203b-0674-5bed-bb07-1a78e0eb3625
-- title:
--   Eden Verified: p06 radius Evolution antitone On
-- statement:
--   The Eden Verified construction uses the p06 radius Evolution antitone On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L912-L915
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L912-L915

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p06_radiusEvolution_antitoneOn :
    ∀ {R : ℝ} (hR : Real.sqrt 2 ≤ R),
    AntitoneOn (fun t => radiusEvolution t R) (Ici 0) := by sorry
