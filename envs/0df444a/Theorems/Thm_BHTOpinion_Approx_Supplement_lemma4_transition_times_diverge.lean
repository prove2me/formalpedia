-- Prove2me | Theorems.Thm_BHTOpinion_Approx_Supplement_lemma4_transition_times_diverge
-- name    : BHTOpinion.Approx.Supplement.lemma4_transition_times_diverge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:54:21.566267+00:00
-- url     : https://prove2.me/theorems/851f9273-4a3d-4994-b6ae-1d9fde3d1b6c
-- title:
--   Lemma 4 — nonproblematic infinite switching cannot accumulate; unique global solution; ẋ does not tend to 0
-- statement:
--   Consider $n$ agents following (2.1). Suppose the recursive construction of Appendix A, started from $\tilde x\in X_{G_0}$, never meets a problematic boundary point and produces an infinite sequence of transition times: there are graphs $G_0,G_1,\dots$, times $0=t_0<t_1<t_2<\cdots$ and a trajectory $x$ forming an infinite run (on $[t_k,t_{k+1}]$, $x$ follows $\dot x=-L_{G_k}x$ inside $X_{G_k}$ until it first reaches $\partial X_{G_k}$), and every transition at $x(t_{k+1})$ from $X_{G_k}$ to $X_{G_{k+1}}$ is nonproblematic. Then:
--   1. the transition times diverge,
--   $$
--   t_k\longrightarrow\infty \quad (k\to\infty);
--   $$
--   2. the constructed trajectory $x$ is a solution of (2.1) on $[0,\infty)$, and every solution $y$ of (2.1) with $y(0)=\tilde x$ coincides with $x$ on $[0,\infty)$;
--   3. $\dot x(t)$ does not converge to $0$ as $t\to\infty$: there is $\varepsilon>0$ such that at arbitrarily large times $s$ at which $x$ is differentiable, $\|\dot x(s)\|_\infty>\varepsilon$.
--
--   Together with the a.e. absence of problematic points, the lemma closes the proof of Theorem 1: an infinite nonproblematic switching sequence cannot accumulate at a finite time, so the construction defines the unique solution on all of $[0,\infty)$.
--
--   The lemma is a conditional statement about a hypothetical infinite run; the paper does not claim that such runs exist.
--
--   **Formalization Note** Solutions of (2.1) are the published `BHTOpinion.Approx.IsDiscreteSolution` (continuity on $[0,\infty)$, integrability of the integrand, the integral identity at every $t\ge0$). Only the values of $x$ on the constructed intervals are constrained by the hypotheses, so conclusion 2 genuinely depends on conclusion 1.
--
--   Differences from the source:
--   - encoding: ẋ(t) does not converge to 0 when t → ∞ → there is ε > 0 such that at arbitrarily large times s the trajectory has a derivative v with ‖v‖ > ε (sup norm); reason: x is not differentiable at the transition times; the velocity is read at differentiability times, which is what convergence of ẋ means for this piecewise smooth trajectory
--   - encoding: transition times t₀, t₁, … → t 0 = 0 is the start time and t (k+1) are the transitions; reason: the construction text calls the first transition t₁; indexing from the start time makes the two labelings agree
--   - reading: there exists a unique solution x, defined for all t ≥ 0 → the constructed trajectory x is a solution of (2.1) on [0, ∞) and every solution with the same initial value agrees with it on [0, ∞); reason: the solution the lemma refers to is the one produced by the construction; the Lean names it, which implies the bare existence-and-uniqueness claim
-- source:
--   Blondel, Hendrickx, Tsitsiklis, Continuous-time average-preserving opinion dynamics with opinion-dependent communications, SIAM J. Control Optim. 48 (2010), DOI 10.1137/090766188, Lemma 4, p. 5235 (PDF 22); construction pp. 5234–5235 (PDF 21–22); proof pp. 5235–5236 (PDF 22–23)

import Mathlib
import Definitions.Def_BHTOpinion_Approx_Discrete
import Definitions.Def_BHTOpinion_Approx_Supplement_Cells

namespace BHTOpinion.Approx.Supplement

theorem lemma4_transition_times_diverge {n : ℕ} (x₀ : Fin n → ℝ) (G : ℕ → SimpleGraph (Fin n))
    (t : ℕ → ℝ) (x : ℝ → Fin n → ℝ) (hrun : IsCellRun x₀ G t x)
    (hnp : ∀ k : ℕ, IsNonproblematicSwitch (G k) (G (k + 1)) (x (t (k + 1)))) :
    Filter.Tendsto t Filter.atTop Filter.atTop ∧
      (BHTOpinion.Approx.IsDiscreteSolution x ∧
        ∀ y : ℝ → Fin n → ℝ, BHTOpinion.Approx.IsDiscreteSolution y → y 0 = x₀ →
          ∀ s : ℝ, 0 ≤ s → y s = x s) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ T : ℝ, ∃ s : ℝ, T ≤ s ∧ ∃ v : Fin n → ℝ, HasDerivAt x v s ∧ ε < ‖v‖ := by sorry

end BHTOpinion.Approx.Supplement
