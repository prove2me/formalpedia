-- Prove2me | Theorems.Thm_BartlettNN_Margin_Minf_squash_le_Minf_quantized
-- name    : BartlettNN.Margin.Minf_squash_le_Minf_quantized
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:06:03.250328+00:00
-- url     : https://prove2.me/theorems/6f1c718c-8594-406b-a335-52eaaa5eee51
-- title:
--   Proof of Theorem 2 — M∞(π_γ(H), γ/2, 2m) ≤ M∞(F, γ/2, 2m)
-- statement:
--   Let $H$ be a class of real functions on $X$, $\gamma>0$, and $F=Q_{\gamma/8}(\pi_\gamma(H))$. For every $m$,
--   $$
--   \mathcal M_\infty(\pi_\gamma(H),\gamma/2,2m)\ \le\ \mathcal M_\infty(F,\gamma/2,2m),
--   $$
--   where $\mathcal M_\infty$ is the $\ell_\infty$ packing number (maximum over samples of length $2m$ of the largest $\gamma/2$-separated subset). Quantizing a squashed class does not destroy separation at scale $\gamma/2$.
--
--   **Formalization Note** "$\alpha$-separated" is read as $d_{\ell_\infty(x)}(f,g)\ge\alpha$ for distinct elements; packing numbers are valued in `ℕ∞`. The paper's standing assumption $\gamma<1$ is not needed and not imposed.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 528, proof of Theorem 2, display after 'It is easy to see that'

import Mathlib
import Definitions.Def_BartlettNN_Margin_Classification
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_Margin_Squash
import Definitions.Def_BartlettNN_Margin_Covering

open MeasureTheory

namespace BartlettNN.Margin

/-- **Proof of Theorem 2** (Bartlett 1998, p. 528, "It is easy to see that"). For `γ > 0`, with
`F = Q_{γ/8}(π_γ(H))`, `M∞(π_γ(H), γ/2, 2m) ≤ M∞(F, γ/2, 2m)`. -/
theorem Minf_squash_le_Minf_quantized {X : Type*} (H : Set (X → ℝ)) (γ : ℝ) (hγ : 0 < γ)
    (m : ℕ) :
    Minf (squashClass γ H) (γ / 2) (2 * m)
      ≤ Minf ((fun f => quantize (γ / 8) ∘ f) '' squashClass γ H) (γ / 2) (2 * m) := by sorry

end BartlettNN.Margin
