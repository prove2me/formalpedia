-- Prove2me | Theorems.Thm_BartlettNN_Sigmoid_lemma23_pdim_cover
-- name    : BartlettNN.Sigmoid.lemma23_pdim_cover
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:39:28.30799+00:00
-- url     : https://prove2.me/theorems/d7b34ba8-5ed9-44cb-9ea1-6e4ec743df10
-- title:
--   Lemma 23 — pseudodimension bounds strict ℓ∞ covers
-- statement:
--   Let $F$ be a nonempty class of $[-M/2,M/2]$-valued functions, $M>0$, with finite pseudodimension $d=\operatorname{dim}_P(F)\ge1$. For every sample length $m\ge d$ and every scale $0<\gamma<emM/d$,
--
--   $$N_\infty(F,\gamma,m)<\infty,\qquad \log N_\infty(F,\gamma,m)<d\log\!\left(\frac{e m M}{\gamma d}\right).$$
--
--   This is the covering estimate the paper attributes to Haussler and Long [20]; it is the bridge from the pseudodimension of the first-layer class to the covering numbers in the proof of Corollary 24.
--
--   **Formalization Note.** Corrections of the printed statement, which reads "for any $m\ge d$ and any $\gamma\ge0$": (i) $\gamma>0$, since the right side is undefined at $\gamma=0$; (ii) $d\ge1$, since at $d=0$ the right side is $0$ while $N_\infty\ge1$; (iii) $\gamma<emM/d$, since for larger $\gamma$ the right side is $\le0$ while $\log N_\infty\ge0$, so the strict inequality fails. On $(M/2,emM/d)$ the bound holds with $N_\infty=1$, so (iii) removes exactly the range where the printed bound is false. $F$ nonempty and $M>0$ are the meaningful case of the hypotheses. The paper's bare "log" is taken as $\ln$ on both sides, which does not change the inequality. $N_\infty$ is the external strict $\ell_\infty$ cover number, maximised over samples of length $m$, valued in $\mathbb N\cup\{\infty\}$.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 533, Lemma 23 [20]; https://doi.org/10.1109/18.661502

import Mathlib
import Definitions.Def_BartlettNN_Sigmoid_Fat
import Definitions.Def_BartlettNN_FatNet_coverNum

namespace BartlettNN.Sigmoid

/-- Lemma 23 [20], p. 533, for positive scales below `emM/d`, outside which the printed strict bound is false. -/
theorem lemma23_pdim_cover :
    ∀ {X : Type} (F : Set (X → ℝ)) (M γ : ℝ) (d m : ℕ),
      F.Nonempty →
      (∀ f ∈ F, ∀ x, f x ∈ Set.Icc (-M / 2) (M / 2)) →
      pdim F = d → 0 < M → 0 < γ → 1 ≤ d → d ≤ m →
      γ < Real.exp 1 * m * M / d →
      ∃ K : ℕ, BartlettNN.Margin.Ninf F γ m = K ∧
        Real.log K < d * Real.log (Real.exp 1 * m * M / (γ * d)) := by sorry

end BartlettNN.Sigmoid
