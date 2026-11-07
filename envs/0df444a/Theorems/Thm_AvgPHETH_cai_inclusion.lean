-- Prove2me | Theorems.Thm_AvgPHETH_cai_inclusion
-- name    : AvgPHETH.cai_inclusion
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:37:26.075539+00:00
-- url     : https://prove2.me/theorems/3ef527c8-d24b-48c4-84d5-ffebb8ce49a6
-- title:
--   Proof of Lemma 6.5 — Cai's relativized inclusion $\mathrm S_2\cdot\mathrm P^{A_{j-1}}\subseteq\mathrm{ZPP}^{A_j}$
-- statement:
--   For $j\ge1$ let $C_j^O$ be a $\Sigma_j^{p,O}$-complete language, let $C_0^O=\emptyset$, and write $A_j=O\oplus C_j^O$. Then
--
--   $$\mathrm S_2\cdot\mathrm P^{A_{j-1}}\subseteq\mathrm{ZPP}^{A_j}.$$
--
--   The paper imports this from [Cai07] for use in removing the symmetric alternations.
--
--   Differences from the source:
--   - generalization: $1\le j<d$ → every $j\ge1$; reason: the inclusion involves no $d$, and the range on the page is the one the proof uses
--   - encoding: $\mathrm{ZPP}^{A}$ with a zero-error machine → the published KarpLiptonOM.ZPP, whose clock holds for every oracle; reason: a machine can clock itself with its own polynomial, so the class is unchanged
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), proof of Lemma 6.5, p.29 (PDF 31)

import Mathlib
import Definitions.Def_AvgPHETH_S2P
import Definitions.Def_AvgPHETH_oJoin
import Definitions.Def_AvgPHETH_IsSigmaComplete
import Definitions.Def_KarpLiptonOM_ZPP
open KarpLiptonOM

namespace AvgPHETH

/-- **Cai's relativized inclusion [Cai07]**, as used in the proof of Lemma 6.5 (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.29 (PDF 31)):
`S₂ · P^{A_{j−1}} ⊆ ZPP^{A_j}`, where `A_j = O ⊕ C_j^O`, `C_j^O` is a `Σ_j^{p,O}`-complete language for `j ≥ 1`, and `C_0^O = ∅`.

**Formalization Note** The page writes `1 ≤ j < d`; the inclusion holds for every `j ≥ 1` and involves no `d`. -/
theorem cai_inclusion (O : Set (List Bool)) (j : ℕ) (hj : 1 ≤ j) (C C' : Set (List Bool))
    (hC : (j = 1 ∧ C = ∅) ∨ (2 ≤ j ∧ IsSigmaComplete O (j - 1) C))
    (hC' : IsSigmaComplete O j C') (L : Set (List Bool)) (hL : S2P (oJoin O C) L) :
    ZPP (oJoin O C') L := by sorry

end AvgPHETH
