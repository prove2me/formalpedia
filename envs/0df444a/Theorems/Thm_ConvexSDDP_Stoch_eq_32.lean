-- Prove2me | Theorems.Thm_ConvexSDDP_Stoch_eq_32
-- name    : ConvexSDDP.Stoch.eq_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:59:10.122372+00:00
-- url     : https://prove2.me/theorems/438f19b6-fcd1-4caa-9667-bf20bbe1bc60
-- title:
--   (32), p. 21 — at the iterations where a node is selected in the block, its approximation becomes exact
-- statement:
--   Assume $(H_2)$, fix choice rules, let the selection process be $\tau$-admissible, and let every sample path carry a run of the algorithm. Let $n$ be a non-leaf node and assume that almost surely, for every child $m\in r(n)$,
--   $$\lim_{k\to+\infty}V_m\big(x^{k\tau}_m\big)-V^{k\tau}_m\big(x^{k\tau}_m\big)=0.$$
--   Then almost surely
--   $$V_n\big(x^{k\tau}_n\big)-V^{k\tau}_n\big(x^{k\tau}_n\big)\ \xrightarrow[\ \tilde y^k_n=1\ ]{k\to\infty}\ 0,$$
--   that is, the convergence holds along the iterations $k$ with $\tilde y^k_n=1$.
--
--   This is the first half of the inductive step of Theorem 3.1; the second half treats the iterations with $\tilde y^k_n=0$.
--
--   **Formalization Note** Index shift: the paper's $V^{k\tau}_n$ is `(r ω).Vc (k * τ + 1) n`. "As $k\to\infty$ with $\tilde y^k_n=1$" is the filter `atTop ⊓ 𝓟 {k | ỹ^k_n(ω) = 1}`; on a path with finitely many such $k$ the statement is empty, as on the page.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 21, (32), proof of Theorem 3.1

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Stoch_Tree
import Definitions.Def_ConvexSDDP_Stoch_Model
import Definitions.Def_ConvexSDDP_Stoch_Run
import Definitions.Def_ConvexSDDP_Stoch_Selection
open StochasticProg.Multistage MeasureTheory ProbabilityTheory Filter Topology

namespace ConvexSDDP.Stoch

theorem eq_32 {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p) (hH2 : M.H2)
    (R : Rules T d p) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → T.Node → Bool) (hY : ∀ k, Measurable (Y k)) (τ : ℕ)
    (hadm : IsAdmissible T P Y τ) (r : Ω → RunData T d p)
    (hr : ∀ ω, IsTreeRun M R (fun k => Y k ω) (r ω))
    (n : T.Node) (hn : ¬ IsLeaf T n)
    (hind : ∀ᵐ ω ∂P, ∀ m ∈ T.children n,
      Tendsto (fun k => M.V m ((r ω).x (k * τ) m) - (r ω).Vc (k * τ + 1) m ((r ω).x (k * τ) m))
        atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun k => M.V n ((r ω).x (k * τ) n) - (r ω).Vc (k * τ + 1) n ((r ω).x (k * τ) n))
      (atTop ⊓ 𝓟 {k | ytilde Y τ k n ω = true}) (𝓝 0) := by sorry

end ConvexSDDP.Stoch
