-- Prove2me | Theorems.Thm_BartlettNN_Margin_fat_quantized_le_fat_squash
-- name    : BartlettNN.Margin.fat_quantized_le_fat_squash
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:05:45.838593+00:00
-- url     : https://prove2.me/theorems/dab8916b-b49b-499c-89eb-26a7c032783a
-- title:
--   Proof of Theorem 2 — fat_F(γ/8) ≤ fat_{π_γ(H)}(γ/16) for F = Q_{γ/8}(π_γ(H))
-- statement:
--   Let $H$ be a class of real functions on $X$ and $\gamma>0$. Let $F=Q_{\gamma/8}(\pi_\gamma(H))=\{Q_{\gamma/8}\circ f : f\in\pi_\gamma(H)\}$ be the class of quantized squashed functions. Then
--   $$
--   \operatorname{fat}_F(\gamma/8)\ \le\ \operatorname{fat}_{\pi_\gamma(H)}(\gamma/16).
--   $$
--   Quantization lowers the scale at which shattering can occur by at most half a quantization step; this is what lets the finite-valued class $F$ inherit the fat-shattering bound of $H$.
--
--   **Formalization Note** The paper justifies this by the display $|Q_{\gamma/8}(a)-Q_{\gamma/8}(b)|<|a-b|+\gamma/16$, which is a slip: since $x-\alpha/2\le Q_\alpha(x)<x+\alpha/2$, the correct bound is $|a-b|+\gamma/8$ (for $\alpha=\gamma/8$, $b=\alpha/2$, $a=\alpha/2+\epsilon$ one gets $Q(b)=0$, $Q(a)=\alpha$). Only the conclusion is stated here, and it is true as printed. The paper's standing assumption $\gamma<1$ is not needed and not imposed.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 528, proof of Theorem 2, display after 'we have'

import Mathlib
import Definitions.Def_BartlettNN_Margin_Classification
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_Margin_Squash
import Definitions.Def_BartlettNN_Margin_Covering

open MeasureTheory

namespace BartlettNN.Margin

/-- **Proof of Theorem 2** (Bartlett 1998, p. 528, display after "we have"). For `γ > 0`, the
quantized class `F = Q_{γ/8}(π_γ(H))` satisfies `fat_F(γ/8) ≤ fat_{π_γ(H)}(γ/16)`. -/
theorem fat_quantized_le_fat_squash {X : Type*} (H : Set (X → ℝ)) (γ : ℝ) (hγ : 0 < γ) :
    fat ((fun f => quantize (γ / 8) ∘ f) '' squashClass γ H) (γ / 8)
      ≤ fat (squashClass γ H) (γ / 16) := by sorry

end BartlettNN.Margin
