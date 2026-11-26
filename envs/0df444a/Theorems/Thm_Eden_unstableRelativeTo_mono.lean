-- Prove2me | Theorems.Thm_Eden_unstableRelativeTo_mono
-- name    : Eden.unstableRelativeTo_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:28:14.980729+00:00
-- url     : https://prove2.me/theorems/dfab3190-a154-54bf-9e85-26356a09e338
-- title:
--   Eden: unstable Relative To mono
-- statement:
--   The Eden construction uses the unstable Relative To mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NonlinearInstability.lean#L119-L124
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NonlinearInstability.lean#L119-L124

import Definitions.Def_Eden_InstabilityGeometry
import Definitions.Def_Eden_NonlinearInstability
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.unstableRelativeTo_mono (c : ℝ) {B C K : Set PhaseSpace}
    (hBC : B ⊆ C) (h : UnstableRelativeTo c B K) : UnstableRelativeTo c C K := by sorry
