-- Prove2me | Theorems.Thm_BitcoinBackboneProb_backbone_failure_le
-- name    : BitcoinBackboneProb.backbone_failure_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:24:17.615388+00:00
-- url     : https://prove2.me/theorems/f6a8074a-5f76-4461-9f3a-e41006b581f2
-- title:
--   Any deterministic consequence of typicality fails with probability at most (L+1)² e^(−rate(λ+1))
-- statement:
--   For any property $Q$ of executions that holds for every legal typical execution (`hdet`): the probability that some network behaviour and adversarial chain choices produce a legal induced execution violating $Q$ is at most $(L+1)^2 e^{-\text{rate}(\lambda+1)}$.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
import Definitions.Def_BitcoinBackbone
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.backbone_failure_le (n t : ℕ) (p : unitInterval) (lam L : ℕ)
    (hlam : 2 ≤ lam) (hm : 0 < margin n t p)
    (hk : 4 * t * (p : ℝ) ≤ ((lam : ℝ) - 3) * margin n t p)
    (Q : BitcoinBackbone.Execution → Prop)
    (hdet : ∀ E : BitcoinBackbone.Execution, E.Legal → E.Typical lam → Q E) :
    (P n t p).real {ω | ∃ base advParent : ℕ → ℕ → BitcoinBackbone.Chain,
      (toExecution ω L base advParent).Legal ∧ ¬ Q (toExecution ω L base advParent)} ≤
      ((L : ℝ) + 1) ^ 2 * Real.exp (-rate n t p * ((lam : ℝ) + 1)) := by sorry
