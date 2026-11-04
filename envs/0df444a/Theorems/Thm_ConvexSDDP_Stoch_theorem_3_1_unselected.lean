-- Prove2me | Theorems.Thm_ConvexSDDP_Stoch_theorem_3_1_unselected
-- name    : ConvexSDDP.Stoch.theorem_3_1_unselected
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T02:41:13.393859+00:00
-- url     : https://prove2.me/theorems/f1216b95-e374-425f-b55e-ca985792a733
-- title:
--   Proof of Theorem 3.1, pp. 21–22 — exactness at the selected blocks extends to all blocks
-- statement:
--   This is the last step of the proof of Theorem 3.1 (pp. 21–22): exactness of the cuts at the iterations where a node is selected propagates to all iterations.
--
--   Consider the multistage stochastic convex program (19) on a finite scenario tree under assumptions $(H_2)$, and the decomposition algorithm of pp. 13–14 run with fixed deterministic choice rules (footnote 6) along a $\tau$-admissible selection process $(y^k)_{k\in\mathbb N}$ (Definition 1), with $\tilde y^k_n=\max\{y^{k\tau}_n,\dots,y^{k\tau+\tau-1}_n\}$ as in (23). Let $n$ be a node that is not a leaf, and assume that (32) holds at $n$, namely that $\mathbb P$-almost surely
--   $$\lim_{k\to+\infty,\ \tilde y^k_n=1}\ V_n\big(x^{k\tau}_n\big)-V^{k\tau}_n\big(x^{k\tau}_n\big)=0 .$$
--   Then, $\mathbb P$-almost surely, the convergence holds along all iterations:
--   $$\lim_{k\to+\infty}\ V_n\big(x^{k\tau}_n\big)-V^{k\tau}_n\big(x^{k\tau}_n\big)=0 .$$
--
--   In the paper this is the paragraph beginning "Now we prove that the values also converge for the iterations $k$ such that $\tilde y^k_n=0$". Together with Lemma 3.2 and (32) it closes the backward induction on the tree that proves Theorem 3.1.
--
--   **Formalization Note** Index shift: the paper's $V^{k\tau}_n$ is `(r ω).Vc (k * τ + 1) n`. The limit along the selected blocks is the filter `atTop ⊓ 𝓟 {k | ytilde Y τ k n ω = true}` (trivially satisfied when $n$ is selected only finitely often). Limits are taken in $\overline{\mathbb R}$. The hypotheses are those of Theorem 3.1: $(H_2)$, fixed choice rules, a run of the algorithm on every sample path, measurable selections and $\tau$-admissibility.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, pp. 21–22, proof of Theorem 3.1 (paragraph after (32), eq. (33))

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Stoch_Tree
import Definitions.Def_ConvexSDDP_Stoch_Model
import Definitions.Def_ConvexSDDP_Stoch_Run
import Definitions.Def_ConvexSDDP_Stoch_Selection
open StochasticProg.Multistage MeasureTheory ProbabilityTheory Filter Topology

namespace ConvexSDDP.Stoch

theorem theorem_3_1_unselected {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p) (hH2 : M.H2)
    (R : Rules T d p) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → T.Node → Bool) (hY : ∀ k, Measurable (Y k)) (τ : ℕ)
    (hadm : IsAdmissible T P Y τ) (r : Ω → RunData T d p)
    (hr : ∀ ω, IsTreeRun M R (fun k => Y k ω) (r ω))
    (n : T.Node) (hn : ¬ IsLeaf T n)
    (h32 : ∀ᵐ ω ∂P, Tendsto
      (fun k => M.V n ((r ω).x (k * τ) n) - (r ω).Vc (k * τ + 1) n ((r ω).x (k * τ) n))
      (atTop ⊓ 𝓟 {k | ytilde Y τ k n ω = true}) (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun k => M.V n ((r ω).x (k * τ) n) - (r ω).Vc (k * τ + 1) n ((r ω).x (k * τ) n))
      atTop (𝓝 0) := by sorry

end ConvexSDDP.Stoch
