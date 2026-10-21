-- Prove2me | Theorems.Thm_EssCheck_Accuracy_lemma_2
-- name    : EssCheck.Accuracy.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:09.645492+00:00
-- url     : https://prove2.me/theorems/b2c94600-6ba6-435e-a803-b742412b4d5a
-- title:
--   Lemma 2 — more accurate checks increase equilibrium research effort locally
-- statement:
--   Fix $\beta_0<1$ and an interior equilibrium-effort path $x^*(\beta)$ continuous from the right at $\beta_0$. Assume equation (4) is strict in every state with positive probability, so a small increase in accuracy leaves the hybrid and pooling sets unchanged. If $c''(x^*(\beta_0))>0$, then the right derivative exists and
--   $$\frac{\partial x^*}{\partial\beta}\bigg|_{\beta_0}=\frac{\sum_{i\in H}p_i^0l_i+\sum_{i\in P}p_i^0\bar\alpha v_i}{c''(x^*(\beta_0))}>0.$$
--   This is the comparative-statics step used by Proposition 1.
--
--   **Formalization Note** The path satisfies the equilibrium first-order condition at the base point and for all sufficiently nearby accuracy values. The positive second derivative and continuous path make explicit premises used by the paper's implicit-function argument.
-- source:
--   Schuett & Wipusanawan, Essentiality Checks for Standard Essential Patents, TILEC Discussion Paper DP 2023-21 (Dec. 2023; SSRN 4688864), p. 20 (PDF 21), Lemma 2 and displayed derivative in its proof

import Mathlib
import Definitions.Def_EssCheck_Accuracy_Model

namespace EssCheck.Accuracy

theorem lemma_2 {n : ℕ} (M : Model n) (hS : M.Standing)
    (β0 : ℝ) (hβ0 : 0 ≤ β0) (hβ1 : β0 < 1) (xs : ℝ → ℝ)
    (heq : ∀ᶠ β in nhdsWithin β0 (Set.Ici β0), IsEqEffort M β (xs β))
    (heq0 : IsEqEffort M β0 (xs β0))
    (hcont : ContinuousWithinAt xs (Set.Ici β0) β0)
    (hstrict : ∀ i, (0 < M.pH i ∨ 0 < M.p0 i) → ¬ Eq4 M β0 (xs β0) i)
    (hc2 : 0 < iteratedDeriv 2 M.c (xs β0)) :
    let H := hybridSet M β0 (xs β0)
    let D := ((∑ i ∈ H, M.p0 i * M.l i) +
      (∑ i ∈ Finset.univ \ H, M.p0 i * (M.αbar * M.v i))) /
        iteratedDeriv 2 M.c (xs β0)
    HasDerivWithinAt xs D (Set.Ici β0) β0 ∧ 0 < D := by sorry

end EssCheck.Accuracy
