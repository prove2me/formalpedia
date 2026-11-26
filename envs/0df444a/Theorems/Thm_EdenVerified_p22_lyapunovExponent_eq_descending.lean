-- Prove2me | Theorems.Thm_EdenVerified_p22_lyapunovExponent_eq_descending
-- name    : EdenVerified.p22_lyapunovExponent_eq_descending
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:49:22.304742+00:00
-- url     : https://prove2.me/theorems/93cd8186-8e6f-4ce9-aad3-0db7d79c42e4
-- title:
--   Eden Verified: p22 lyapunov Exponent eq descending
-- statement:
--   The Eden Verified construction uses the p22 lyapunov Exponent eq descending property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1688-L1691
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1688-L1691

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p22_lyapunovExponent_eq_descending :
    ∀ (c : ℝ) (p : PhaseSpace) (i : Fin 5),
    lyapunovExponent c p i = descending (factorExponents c p) i := by sorry
