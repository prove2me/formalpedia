-- Prove2me | Theorems.Thm_BitcoinBackboneProb_map_eval_P
-- name    : BitcoinBackboneProb.map_eval_P
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:12:57.001531+00:00
-- url     : https://prove2.me/theorems/d0b9e4f6-4043-4746-97af-b393e1b1aa9c
-- title:
--   Each round has the round law
-- statement:
--   The image of `P n t p` under $\omega \mapsto \omega_r$ is `roundMeasure n t p`.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.map_eval_P (n t : ℕ) (p : unitInterval) (r : ℕ) :
    (P n t p).map (fun ω => ω r) = roundMeasure n t p := by sorry
