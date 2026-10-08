-- Prove2me | Theorems.Thm_BartlettNN_Margin_Ninf_squash_le_Ninf_quantized
-- name    : BartlettNN.Margin.Ninf_squash_le_Ninf_quantized
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:05:51.265806+00:00
-- url     : https://prove2.me/theorems/db5e8b21-80b6-4d26-bb7a-c7b3ce286704
-- title:
--   Proof of Theorem 2 — N∞(π_γ(H), γ/2, 2m) ≤ N∞(F, γ/4, 2m)
-- statement:
--   Let $H$ be a class of real functions on $X$, $\gamma>0$, and $F=Q_{\gamma/8}(\pi_\gamma(H))$. For every $m$,
--   $$
--   \mathcal N_\infty(\pi_\gamma(H),\gamma/2,2m)\ \le\ \mathcal N_\infty(F,\gamma/4,2m).
--   $$
--   The covering number of the squashed class, which appears in Lemma 4, is thereby bounded by a covering number of a finite-valued class, to which Theorem 5 applies.
--
--   **Formalization Note** Covering numbers are external, strict and valued in `ℕ∞` (see the covering-number definition). The paper's standing assumption $\gamma<1$ is not needed and not imposed.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 528, proof of Theorem 2, display after 'hence'

import Mathlib
import Definitions.Def_BartlettNN_Margin_Classification
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_Margin_Squash
import Definitions.Def_BartlettNN_Margin_Covering

open MeasureTheory

namespace BartlettNN.Margin

/-- **Proof of Theorem 2** (Bartlett 1998, p. 528, display after "hence"). For `γ > 0`, with
`F = Q_{γ/8}(π_γ(H))`, `N∞(π_γ(H), γ/2, 2m) ≤ N∞(F, γ/4, 2m)`. -/
theorem Ninf_squash_le_Ninf_quantized {X : Type*} (H : Set (X → ℝ)) (γ : ℝ) (hγ : 0 < γ)
    (m : ℕ) :
    Ninf (squashClass γ H) (γ / 2) (2 * m)
      ≤ Ninf ((fun f => quantize (γ / 8) ∘ f) '' squashClass γ H) (γ / 4) (2 * m) := by sorry

end BartlettNN.Margin
