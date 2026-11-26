-- Prove2me | Theorems.Thm_Eden_exteriorGrowthRate_basis
-- name    : Eden.exteriorGrowthRate_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:29.701828+00:00
-- url     : https://prove2.me/theorems/c62c7c1e-813d-45da-a5b9-7d569b0e099c
-- title:
--   Eden: exterior Growth Rate basis
-- statement:
--   The Eden construction uses the exterior Growth Rate basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L76-L79
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L76-L79

import Definitions.Def_Eden_ExteriorLimits
import Definitions.Def_Eden_SelectedSums
import Definitions.Def_Eden_KaplanYorke
import Mathlib.Topology.Order.LiminfLimsup
import Definitions.Def_Eden_ExteriorMaximalGrowth
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.exteriorGrowthRate_basis (k : ℕ) (c : ℝ) (p : PhaseSpace) (s : ExteriorIndex k) :
    exteriorGrowthRate k c p (initialExteriorBasisVector k p s) = exteriorRate k c p s := by sorry
