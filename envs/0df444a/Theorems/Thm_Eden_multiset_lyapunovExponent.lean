-- Prove2me | Theorems.Thm_Eden_multiset_lyapunovExponent
-- name    : Eden.multiset_lyapunovExponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:01:50.443462+00:00
-- url     : https://prove2.me/theorems/16616384-8736-471b-9004-ca918c49c0d6
-- title:
--   Eden: multiset lyapunov Exponent
-- statement:
--   The Eden construction uses the multiset lyapunov Exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LyapunovExponents.lean#L82-L87
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LyapunovExponents.lean#L82-L87

import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_Sorting
import Definitions.Def_Eden_LyapunovExponents
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.multiset_lyapunovExponent (c : ℝ) (p : PhaseSpace) :
    Finset.univ.val.map (lyapunovExponent c p) = Finset.univ.val.map (factorExponents c p) := by sorry
