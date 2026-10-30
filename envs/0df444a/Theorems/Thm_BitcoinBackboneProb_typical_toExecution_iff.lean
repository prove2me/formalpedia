-- Prove2me | Theorems.Thm_BitcoinBackboneProb_typical_toExecution_iff
-- name    : BitcoinBackboneProb.typical_toExecution_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:23:06.587904+00:00
-- url     : https://prove2.me/theorems/82bb818a-9754-4db0-bfc4-defc6174c4b9
-- title:
--   Typicality of the induced execution does not depend on the network or the adversary's chain choices
-- statement:
--   `(toExecution ω L base advParent).Typical lam ↔ TypicalTrunc ω lam L`.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
import Definitions.Def_BitcoinBackbone
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.typical_toExecution_iff {n t : ℕ} (ω : Trace n t) (lam L : ℕ)
    (base advParent : ℕ → ℕ → BitcoinBackbone.Chain) :
    (toExecution ω L base advParent).Typical lam ↔ TypicalTrunc ω lam L := by sorry
