-- Prove2me | Theorems.Thm_ConvexSDDP_Stoch_theorem_3_1
-- name    : ConvexSDDP.Stoch.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:01:33.170431+00:00
-- url     : https://prove2.me/theorems/0cbc2ec9-f57a-4042-b120-a37725302a92
-- title:
--   Theorem 3.1, p. 19 — under τ-admissible selection, decisions become optimal and cuts exact almost surely at every node
-- statement:
--   Consider the multistage stochastic convex program (19) on a finite scenario tree under assumptions $(H_2)$, and the decomposition algorithm of pp. 13–14 in which, at each iteration $k$, the whole tree is simulated with the current approximations $V^{k-1}$, and cuts are computed at randomly selected nodes. Assume the choices of minimisers and multipliers are made by fixed deterministic rules (footnote 6), and that the selection process is $\tau$-admissible for some integer $\tau>0$ (Definition 1). Then, $\mathbb P$-almost surely,
--   $$\lim_{k\to+\infty}\ \sum_{m\in r(n)}\frac{\Phi_m}{\Phi_n}W_m\big(x^{k\tau}_n,u^{k\tau}_m\big)-V_n\big(x^{k\tau}_n\big)=0\qquad\text{for every }n\in\mathcal N\setminus\mathcal L,$$
--   and
--   $$\lim_{k\to+\infty}\ V_n\big(x^{k\tau}_n\big)-V^{k\tau}_n\big(x^{k\tau}_n\big)=0\qquad\text{for every }n\in\mathcal N.$$
--   Here $W_m(x,u)=C_m(x,u)+V_m(f_m(x,u))$ is the true cost-to-go (24).
--
--   Along the iterations $k\tau$, the decisions taken at every node become optimal for the true problem, and the cutting-plane approximations become exact at the visited stocks. This covers sampling schemes such as CUPPS and SDDP/DOASA (§3.3) for convex, not necessarily linear, stage problems.
--
--   **Formalization Note** Index shift: the paper's $V^{k\tau}_n$ is `(r ω).Vc (k * τ + 1) n`. The page leaves $n$ free: the first limit is stated for non-leaf nodes (at a leaf the sum is empty and the claim is false), the second for every node (at a leaf it is trivial). Limits are taken in $\overline{\mathbb R}$, so convergence to $0$ forces the differences to be finite from some index on. Hypotheses: $(H_2)$ with the standing data of §3.1 (node probabilities, $x_0\in\mathcal X_0$), fixed choice rules, a run of the algorithm on every sample path, measurable selections and $\tau$-admissibility.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 19, Theorem 3.1

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Stoch_Tree
import Definitions.Def_ConvexSDDP_Stoch_Model
import Definitions.Def_ConvexSDDP_Stoch_Run
import Definitions.Def_ConvexSDDP_Stoch_Selection
open StochasticProg.Multistage MeasureTheory ProbabilityTheory Filter Topology

namespace ConvexSDDP.Stoch

theorem theorem_3_1 {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p) (hH2 : M.H2)
    (R : Rules T d p) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → T.Node → Bool) (hY : ∀ k, Measurable (Y k)) (τ : ℕ)
    (hadm : IsAdmissible T P Y τ) (r : Ω → RunData T d p)
    (hr : ∀ ω, IsTreeRun M R (fun k => Y k ω) (r ω)) :
    ∀ᵐ ω ∂P,
      (∀ n, ¬ IsLeaf T n →
        Tendsto (fun k => (∑ m ∈ T.children n,
            ((M.Φ m / M.Φ n : ℝ) : EReal) * M.W m ((r ω).x (k * τ) n) ((r ω).u (k * τ) m)) -
            M.V n ((r ω).x (k * τ) n)) atTop (𝓝 0)) ∧
      (∀ n, Tendsto
        (fun k => M.V n ((r ω).x (k * τ) n) - (r ω).Vc (k * τ + 1) n ((r ω).x (k * τ) n))
        atTop (𝓝 0)) := by sorry

end ConvexSDDP.Stoch
