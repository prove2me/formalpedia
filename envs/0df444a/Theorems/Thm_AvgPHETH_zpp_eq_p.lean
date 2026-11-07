-- Prove2me | Theorems.Thm_AvgPHETH_zpp_eq_p
-- name    : AvgPHETH.zpp_eq_p
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:37:12.603229+00:00
-- url     : https://prove2.me/theorems/8c823875-33ef-4397-b844-833a84dee968
-- title:
--   Proof of Lemma 6.5 — $\mathrm{ZPP}^{A_j}=\mathrm P^{A_j}$
-- statement:
--   Suppose $\Sigma_d^{p,O}\times\{\mathcal U,\mathcal T\}\subseteq\mathrm{AvgP}^O$ for an oracle $O$ and a fixed $d\ge2$. For $1\le j<d$, with $C_j^O$ a $\Sigma_j^{p,O}$-complete language and $A_j=O\oplus C_j^O$,
--
--   $$\mathrm{ZPP}^{A_j}=\mathrm P^{A_j}.$$
--
--   The proof in the paper builds a pseudorandom generator against $A_j$-oracle circuits from the average-case assumption.
--
--   Differences from the source:
--   - encoding: $\mathrm{ZPP}^{A}$ with a zero-error machine → the published KarpLiptonOM.ZPP, whose clock holds for every oracle; reason: a machine can clock itself with its own polynomial, so the class is unchanged
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), proof of Lemma 6.5, p.29 (PDF 31)

import Mathlib
import Definitions.Def_AvgPHETH_TimesUT
import Definitions.Def_AvgPHETH_SigmaPO
import Definitions.Def_AvgPHETH_PO
import Definitions.Def_AvgPHETH_oJoin
import Definitions.Def_AvgPHETH_IsSigmaComplete
import Definitions.Def_KarpLiptonOM_ZPP
open KarpLiptonOM

namespace AvgPHETH

/-- **`ZPP^{A_j} = P^{A_j}`**, the step of the proof of Lemma 6.5 (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.29 (PDF 31)): if `Σ_d^{p,O} × {U, T} ⊆ AvgP^O` for a fixed `d ≥ 2`, then
`ZPP^{A_j} = P^{A_j}` for `1 ≤ j < d`, where `A_j = O ⊕ C_j^O` and `C_j^O` is `Σ_j^{p,O}`-complete. -/
theorem zpp_eq_p (O : Set (List Bool)) (d : ℕ) (hd : 2 ≤ d) (hAvg : TimesUT O (SigmaPO O d))
    (j : ℕ) (hj : 1 ≤ j) (hjd : j < d) (C : Set (List Bool)) (hC : IsSigmaComplete O j C)
    (L : Set (List Bool)) : ZPP (oJoin O C) L ↔ PO (oJoin O C) L := by sorry

end AvgPHETH
