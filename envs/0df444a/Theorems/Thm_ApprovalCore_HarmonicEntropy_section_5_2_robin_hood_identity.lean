-- Prove2me | Theorems.Thm_ApprovalCore_HarmonicEntropy_section_5_2_robin_hood_identity
-- name    : ApprovalCore.HarmonicEntropy.section_5_2_robin_hood_identity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:31:18.322187+00:00
-- url     : https://prove2.me/theorems/d8505c49-d242-4e16-bbfc-e80d9218bd29
-- title:
--   §5.2 — the Robin Hood identity $F(\Phi(x)) = F(x) + \|x\|_\infty$
-- statement:
--   For every $x \in \Delta_d$ (zero coordinates allowed),
--   $$F(\Phi(x)) = F(x) + \|x\|_\infty .$$
--   Applying the Robin Hood operator once raises harmonic entropy by exactly the largest coordinate. In a payment system the largest coordinate of a voter's vector is her reserve (by (P2)), so this is the marginal-gain identity behind adding a candidate (Theorem 6.2).
--
--   Differences from the source:
--
--   - encoding: a distribution x ∈ ∆_d with coordinates indexed by [d] → x : Fin d → ℝ with x ∈ stdSimplex ℝ (Fin d), coordinates indexed 0, …, d−1; reason: Mathlib's standard simplex is exactly ∆_d (nonnegative coordinates summing to 1); only the index base changes
--   - encoding: ∥y∥∞ → Mathlib's sup norm ‖y‖ on Fin d → ℝ; reason: the sup norm on a finite product of ℝ is max_j |y_j|, i.e. ∥y∥∞
-- source:
--   Becker, Greger, Peters, Existence of the Core in Approval-Based Committee Elections, STOC 2027 submission (manuscript sha256 7cc237dc…), p. 10 (PDF 11), §5.2, 'Formally, F satisfies F(Φ(x)) = F(x) + ∥x∥∞ for all x ∈ ∆d.'

import Mathlib
import Definitions.Def_ApprovalCore_HarmonicEntropy_RobinHood

namespace ApprovalCore.HarmonicEntropy

/-- §5.2 (p. 10): `F(Φ(x)) = F(x) + ∥x∥∞` for all `x ∈ ∆d`. -/
theorem section_5_2_robin_hood_identity {d : ℕ} (x : Fin d → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin d)) :
    harmonicEntropy (Phi x) = harmonicEntropy x + ‖x‖ := by sorry

end ApprovalCore.HarmonicEntropy
