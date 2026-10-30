-- Prove2me | Theorems.Thm_BitcoinBackboneProb_iIndepFun_rounds
-- name    : BitcoinBackboneProb.iIndepFun_rounds
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:12:16.737649+00:00
-- url     : https://prove2.me/theorems/491012b4-4805-419a-9d5e-937c166c4185
-- title:
--   The rounds of a trace are independent
-- statement:
--   Under `P n t p` the round maps $\omega \mapsto \omega_r$ are mutually independent.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.iIndepFun_rounds (n t : ℕ) (p : unitInterval) :
    ProbabilityTheory.iIndepFun (fun r (ω : Trace n t) => ω r) (P n t p) := by sorry
