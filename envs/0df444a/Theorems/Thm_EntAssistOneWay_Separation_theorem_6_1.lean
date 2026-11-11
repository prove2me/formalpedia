-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_theorem_6_1
-- name    : EntAssistOneWay.Separation.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:36.906189+00:00
-- url     : https://prove2.me/theorems/fa47e510-e0df-4512-add2-67bc35e5e96c
-- title:
--   Theorem 6.1 — explicit groups for the separation
-- statement:
--   For every integer $r\ge1$, let $G_r=H_{2^{2r}}(\mathbb F_3)$ and $\zeta=(0,0,1)$. Then
--   $$|G_r|=3^{2^{2r+1}+1},\qquad\zeta\in Z(G_r),\quad\operatorname{ord}(\zeta)=3,$$
--   and every complex representation of dimension less than $3^{2^{2r}}$ sends $\zeta$ to the identity. Consequently the parameter $D=3^{2^{2r}}$ is admissible in Theorem 5.2.
--
--   This identifies the finite group family and all properties required by the lower-bound theorem, rather than leaving the group unspecified.
--
--   Differences from the source:
--   - generalization: there exists a finite group Gr of the stated size → the particular group Gr = H_(2^(2r))(F₃) has all the stated properties; reason: this is the witness constructed in the proof, and in particular supplies the source existential group
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 36, Theorem 6.1; pp. 37–38, explicit construction

import Definitions.Def_EntAssistOneWay_Separation_Heisenberg

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Theorem 6.1, p. 36, for the explicit group built on p. 37. -/
theorem theorem_6_1 (r : ℕ) (hr : 1 ≤ r) :
    Fintype.card (SeparationGroup r) = 3 ^ (2 ^ (2 * r + 1) + 1) ∧
      CentralThree (heisenbergZeta (2 ^ (2 * r))) ∧
      DimensionGap (heisenbergZeta (2 ^ (2 * r))) (3 ^ (2 ^ (2 * r))) := by sorry

end

end EntAssistOneWay.Separation
