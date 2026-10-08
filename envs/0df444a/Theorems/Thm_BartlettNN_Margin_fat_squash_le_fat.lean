-- Prove2me | Theorems.Thm_BartlettNN_Margin_fat_squash_le_fat
-- name    : BartlettNN.Margin.fat_squash_le_fat
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:06:14.976047+00:00
-- url     : https://prove2.me/theorems/efda2dd7-795a-4fe4-97c0-9fa8c0f1feaf
-- title:
--   Proof of Theorem 2 — fat_{π_γ(H)}(γ/16) ≤ fat_H(γ/16)
-- statement:
--   Let $H$ be a class of real functions on $X$ and $\gamma>0$. Then
--   $$
--   \operatorname{fat}_{\pi_\gamma(H)}(\gamma/16)\ \le\ \operatorname{fat}_H(\gamma/16).
--   $$
--   Squashing a class to $[-\gamma,\gamma]$ cannot increase its fat-shattering dimension at a scale below $\gamma$; this is the last step of the proof of Theorem 2.
--
--   **Formalization Note** Both sides are valued in `ℕ∞`. The paper's standing assumption $\gamma<1$ is not needed and not imposed.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 528, proof of Theorem 2, last sentence

import Mathlib
import Definitions.Def_BartlettNN_Margin_Classification
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_Margin_Squash
import Definitions.Def_BartlettNN_Margin_Covering

open MeasureTheory

namespace BartlettNN.Margin

/-- **Proof of Theorem 2** (Bartlett 1998, p. 528, last sentence). For `γ > 0`,
`fat_{π_γ(H)}(γ/16) ≤ fat_H(γ/16)`. -/
theorem fat_squash_le_fat {X : Type*} (H : Set (X → ℝ)) (γ : ℝ) (hγ : 0 < γ) :
    fat (squashClass γ H) (γ / 16) ≤ fat H (γ / 16) := by sorry

end BartlettNN.Margin
