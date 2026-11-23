-- Prove2me | Theorems.Thm_FirstPrice_affine_procurement
-- name    : FirstPrice.affine_procurement
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:50:41.841348+00:00
-- url     : https://prove2.me/theorems/4421ffa5-479d-4f36-9c46-f71f621b5da5
-- title:
--   Affine transfer from a $[0,1]$ value auction to procurement on $[L,U]$
-- statement:
--   Fix $0<L<U$, and let $A=U-L$. Start with a finite independent-private-value first-price auction whose declared values lie in $[0,1]$ and an exact mixed equilibrium with nonnegative bids and no overbidding. Apply the maps
--   $$c_i=U-Av_i,\qquad b_i^P=U-A b_i^V$$
--   to values and bids, with the tie rule transported by the inverse affine map. The result is a procurement instance with costs and used bids in $[L,U]$ and a mixed equilibrium for all deviations in $[L,U]$. Moreover, its expected costs are finite, its expected optimum has positive real value, and
--   $$
--   \mathbb E[c^{\mathrm{eq}}]=U-A\,\mathbb E[v^{\mathrm{eq}}],
--   \qquad
--   \mathbb E[c^\star]=U-A\,\mathbb E[v^\star].
--   $$
--   This isolates the measure-theoretic affine change of variables in Remark 4.2, including the reversal of lowest and highest bids and preservation of interim winning probabilities and utilities.
--
--   **Formalization Note** The two displayed equations are stated for `ENNReal.toReal`, with finiteness supplied separately. The strict interval assumption makes the affine inverse available; the degenerate case $L=U$ is handled directly and needs no division by zero.
-- source:
--   Palazzotto and Cristi, *At What Cost? (In)efficiency in First-Price Procurement Auctions*, STOC 2027 submission 293, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, p. 9 (printed p. 7), Remark 4.2; the same affine map appears in the proof of Theorem 4.1 on p. 9.

import Mathlib
import Definitions.Def_FirstPrice_ValueAuction
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_StandardAuction

open MeasureTheory ProbabilityTheory
open scoped Classical

theorem FirstPrice.affine_procurement (L U : ℝ) (hL : 0 < L) (hLU : L < U) {n : ℕ}
    (D : ProcurementPoA.DeterministicCap.IndependentTypes n)
    (τ : ProcurementPoA.DeterministicCap.TieRule n)
    (σ : ProcurementPoA.DeterministicCap.MixedProfile n)
    (hval : ∀ i, D.types i ⊆ Set.Icc 0 1) (heq : IsBNE D τ σ) :
    ∃ (Dp : ProcurementPoA.DeterministicCap.IndependentTypes n)
      (τp : ProcurementPoA.DeterministicCap.TieRule n)
      (σp : ProcurementPoA.DeterministicCap.MixedProfile n),
      ProcurementPoA.DeterministicCap.InCostInterval Dp L U ∧
      ProcurementPoA.DeterministicCap.Supplement.IsBidSetBNE Dp τp σp (Set.Icc L U) ∧
      ProcurementPoA.DeterministicCap.Supplement.standardSocialCost Dp τp σp ≠ ⊤ ∧
      ProcurementPoA.DeterministicCap.optimalSocialCost Dp ≠ ⊤ ∧
      0 < (ProcurementPoA.DeterministicCap.optimalSocialCost Dp).toReal ∧
      (ProcurementPoA.DeterministicCap.Supplement.standardSocialCost Dp τp σp).toReal =
        U - (U - L) * (welfare D τ σ).toReal ∧
      (ProcurementPoA.DeterministicCap.optimalSocialCost Dp).toReal =
        U - (U - L) * (optimalWelfare D).toReal := by sorry
