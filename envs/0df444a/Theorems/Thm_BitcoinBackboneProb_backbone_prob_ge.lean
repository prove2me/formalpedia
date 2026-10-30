-- Prove2me | Theorems.Thm_BitcoinBackboneProb_backbone_prob_ge
-- name    : BitcoinBackboneProb.backbone_prob_ge
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:24:47.819025+00:00
-- url     : https://prove2.me/theorems/9c27cc15-532a-4c22-bf0b-af3395e7bafb
-- title:
--   With probability at least 1 − (L+1)² e^(−rate(λ+1)), every legal induced execution has every typicality consequence
-- statement:
--   For any $Q$ with `hdet`: with probability at least $1 - (L+1)^2 e^{-\text{rate}(\lambda+1)}$, for all `base` and `advParent` (an adaptive adversary), a legal induced execution satisfies $Q$. With $Q$ the backbone mission's common prefix, chain growth or chain quality, this is the paper's Theorem: the properties hold except with probability exponentially small in $\lambda$, under honest majority.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
import Definitions.Def_BitcoinBackbone
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.backbone_prob_ge (n t : ℕ) (p : unitInterval) (lam L : ℕ)
    (hlam : 2 ≤ lam) (hm : 0 < margin n t p)
    (hk : 4 * t * (p : ℝ) ≤ ((lam : ℝ) - 3) * margin n t p)
    (Q : BitcoinBackbone.Execution → Prop)
    (hdet : ∀ E : BitcoinBackbone.Execution, E.Legal → E.Typical lam → Q E) :
    1 - ((L : ℝ) + 1) ^ 2 * Real.exp (-rate n t p * ((lam : ℝ) + 1)) ≤
      (P n t p).real {ω | ∀ base advParent : ℕ → ℕ → BitcoinBackbone.Chain,
        (toExecution ω L base advParent).Legal → Q (toExecution ω L base advParent)} := by sorry
