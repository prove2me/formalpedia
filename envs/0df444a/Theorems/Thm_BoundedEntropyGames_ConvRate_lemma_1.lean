-- Prove2me | Theorems.Thm_BoundedEntropyGames_ConvRate_lemma_1
-- name    : BoundedEntropyGames.ConvRate.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:35.490609+00:00
-- url     : https://prove2.me/theorems/bd1937d8-11b2-4217-b11f-74360ca5b89f
-- title:
--   Lemma 1, p. 9 — three properties of the total variation distance
-- statement:
--   Let $E$ and $F$ be finite sets, $p_E,q_E$ pmfs on $E$, and $p_{F|E},q_{F|E}$ conditional pmfs (for each $e$, $p_{F|E}(\cdot|e)$ is a pmf on $F$). Write $p_Ep_{F|E}$ for the joint pmf $(e,f)\mapsto p_E(e)p_{F|E}(f|e)$ on $E\times F$. Then:
--
--   1. $\|p_Ep_{F|E}-q_Ep_{F|E}\|_{TV}=\|p_E-q_E\|_{TV}$;
--   2. $\|p_Ep_{F|E}-q_Eq_{F|E}\|_{TV}\ge\|p_E-q_E\|_{TV}$;
--   3. for pmfs $p_{E_1},p_{E_2}$ on $E$ and $p_{F_1},q_{F_2}$ on $F$,
--   $$
--   \|p_{E_1}p_{F_1}-p_{E_2}q_{F_2}\|_{TV}\le\|p_{E_1}-p_{E_2}\|_{TV}+\|p_{F_1}-q_{F_2}\|_{TV}.
--   $$
--
--   Properties 1 and 2 carry the per-block simulation bound to the joint law of both players' block actions in the proof of Theorem 6.
--
--   **Formalization Note** A conditional pmf is a kernel $E\to F\to\mathbb R$ every row of which is a pmf.
-- source:
--   Valizadeh, Gohari, Playing Games with Bounded Entropy: Convergence Rate and Approximate Equilibria, arXiv:1902.03676v1, p. 9, Lemma 1

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting

namespace BoundedEntropyGames.ConvRate

/-- Lemma 1, p. 9: three properties of the total variation distance. A conditional pmf
`p_{F|E}` is a kernel `K : E → F → ℝ` whose rows are pmfs, and `p_E p_{F|E}` is the joint pmf
`(e, f) ↦ p_E(e) K(e)(f)` on `E × F`. -/
theorem lemma_1 {E F : Type*} [Fintype E] [Fintype F] :
    (∀ (pE qE : E → ℝ) (K : E → F → ℝ), IsPMF pE → IsPMF qE → (∀ e, IsPMF (K e)) →
      tv (fun z : E × F => pE z.1 * K z.1 z.2) (fun z => qE z.1 * K z.1 z.2) = tv pE qE) ∧
    (∀ (pE qE : E → ℝ) (K L : E → F → ℝ), IsPMF pE → IsPMF qE → (∀ e, IsPMF (K e)) →
      (∀ e, IsPMF (L e)) →
      tv pE qE ≤ tv (fun z : E × F => pE z.1 * K z.1 z.2) (fun z => qE z.1 * L z.1 z.2)) ∧
    (∀ (pE₁ pE₂ : E → ℝ) (pF₁ qF₂ : F → ℝ), IsPMF pE₁ → IsPMF pE₂ → IsPMF pF₁ → IsPMF qF₂ →
      tv (fun z : E × F => pE₁ z.1 * pF₁ z.2) (fun z => pE₂ z.1 * qF₂ z.2)
        ≤ tv pE₁ pE₂ + tv pF₁ qF₂) := by sorry

end BoundedEntropyGames.ConvRate
