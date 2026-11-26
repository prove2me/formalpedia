-- Prove2me | Theorems.Thm_EdenVerified_s04_fderiv_evolution_add
-- name    : EdenVerified.s04_fderiv_evolution_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:51:49.779121+00:00
-- url     : https://prove2.me/theorems/62dc68bb-987c-50d0-9fdd-d9dfa6c17ef9
-- title:
--   Eden Verified: s04 fderiv evolution add
-- statement:
--   The Eden Verified construction uses the s04 fderiv evolution add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1820-L1825
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1820-L1825

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s04_fderiv_evolution_add :
    ∀ (c : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (p : PhaseSpace),
    fderiv ℝ (evolution c (s + t)) p =
      (fderiv ℝ (evolution c t) (evolution c s p)).comp (fderiv ℝ (evolution c s) p) := by sorry
