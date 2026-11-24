-- Prove2me | Theorems.Thm_AuctionDuration_ClearingError_Supplement_theorem_C_1
-- name    : AuctionDuration.ClearingError.Supplement.theorem_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:50:57.8728+00:00
-- url     : https://prove2.me/theorems/9206af4a-3209-42a5-97ed-823a5dc123be
-- title:
--   Theorem C.1 (corrected: masked thresholds) — smoothed viscosity pair, limits and Nash controls
-- statement:
--   Fix $h>0$ and the bounded-intensity canonical game. Let $g^a(x)=x_a(x_a-x_b)$ and $g^b(x)=x_b(x_b-x_a)$. For each positive smoothing index $m$, use the exact affine selector $\lambda^m$, clamp $\Phi_m$, and Hamiltonian $H^{*,m}$ of p.25. There is a unique continuous-in-time polynomial-growth viscosity solution pair $(V^{a,m},V^{b,m})$ on the entire lattice, satisfying
--   $$
--   \partial_sV^{a,m}+H^{*,m}(D_aV^{a,m},D_bV^{a,m},D_bV^{b,m})=0,\quad V^{a,m}(h,x)=g^a(x),
--   $$
--   $$
--   \partial_sV^{b,m}+H^{*,m}(D_bV^{b,m},D_aV^{b,m},D_aV^{a,m})=0,\quad V^{b,m}(h,x)=g^b(x).
--   $$
--   There is one strictly increasing sequence $m_k$ of positive indices and measurable functions $V^a,V^b$ such that, at every $(s,x)\in[0,h]\times\mathbb N^2$ and for both players and both difference directions,
--   $$
--   V^{i,m_k}(s,x)\longrightarrow V^i(s,x),\qquad
--   D_jV^{i,m_k}(s,x)\longrightarrow D_jV^i(s,x).
--   $$
--   There are deterministic measurable threshold fields $\theta^a,\theta^b$ valued in $[\lambda_-,\lambda_+]$, completed by $\lambda_-$ off their own zero-marginal sets. Their induced processes are predictable and progressively measurable. Write $E^i_t=\{D_iV^i(t,x+X_{t-})=0\}$. Under the reference time-probability measure, for every starting count pair the two masked selector sequences have the weak $H^2$ limits
--   $$
--   \lambda^{m_k}(D_iV^{i,m_k}(t,x+X_{t-}))\mathbf1_{E^i_t}
--   \rightharpoonup\theta^i(t,x+X_{t-})\mathbf1_{E^i_t},\qquad i=a,b.
--   $$
--   The bang-bang feedbacks $a^*=\lambda_a^*(DV^a,\theta^a)$ and $b^*=\lambda_b^*(DV^b,\theta^b)$ give a Nash equilibrium against every predictable unilateral deviation, with
--   $$
--   V^{i,x}_h(a^*,b^*)=V^i(0,x),\qquad i=a,b,\quad x\in\mathbb N^2.
--   $$
--   All terminal costs are integrable under the controlled probability laws. This companion theorem includes both uniqueness and convergence clauses; Lemma C.1 supplies its moment estimate. No BSDE solution or equilibrium is assumed.
--
--   **Formalization Note** The natural index n represents the positive paper index n+1. The viscosity predicate uses smooth time tests at each fixed lattice site and the solution's nonlocal differences, in the time-continuous polynomial-growth class of p.28 and pp.29–30. Weak convergence tests against every adapted square-integrable process; pairing the two scalar statements gives the printed vector statement.
--
--   Differences from the source:
--   - reading: canonical compensated pair on p.23 → independent reference Poisson coordinates; reason: the multivariate point-process construction and signed compound-Poisson representation on p.29 use no common jumps; compensators alone would not fix a unique law
--   - encoding: predictable controls and current counts in feedbacks → all bounded predictable deviations and pre-jump count feedbacks; reason: pre-jump evaluation supplies predictable representatives and changes no dt×P equivalence class
--   - encoding: expected terminal costs under controlled probabilities → likelihood-defined laws plus probability and integrability conclusions; reason: the expectations are genuine, rather than default integrals of nonintegrable functions
--   - reading: unique viscosity solution without the function class repeated in the theorem → unique time-continuous polynomial-growth viscosity pair; reason: the p.28 BSDE representation and pp.29–30 estimates fix this class; no finite lattice or assumed solution is substituted
--   - reading: positive-index smoothing written n∈N and final interval written [0,t] → paper index n+1 and time interval [0,h]; reason: 1/n, the positive integers on p.32 and the fixed horizon on p.22 identify the intended domain
--   - reading: difference display prints n→∞ → the same selected subsequence as the values; reason: pp.31,35 explicitly relabel n_k as n, and p.37 states that only subsequential convergence is proved
--   - correction: masked selectors claimed to converge to globally positive-range thresholds → weak limits are masked thresholds; thresholds equal λ_- off the zero sets; reason: a masked sequence vanishes off its zero set, so its weak limit does too; with λ_-=λ_+ and no reference jumps the own marginal is 1+λ_+(h-t)>0, contradicting a globally positive masked limit; p.35 explicitly writes the masked limit; rule (L) ignores threshold completions there
-- source:
--   Jusselin, Mastrolia & Rosenbaum, Optimal auction duration: a price formation viewpoint, arXiv:1906.01713v3, https://arxiv.org/abs/1906.01713v3, pp.25–26, Theorem C.1 and (S^n); pp.28–37, proof and conventions

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Supplement_ProcessSpaces

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace AuctionDuration.ClearingError.Supplement

/-- Theorem C.1, pp.25-26, with the selected-subsequence convention from
pp.31,35,37 and the masked-threshold correction from p.35. The natural index n
represents positive paper index n+1. No BSDE existence premise is assumed. -/
theorem theorem_C_1 (G : Game) (hG : G.Standing) (hh : 0 < G.h) :
    G.WellDefined ∧
    ∃ Vn : ℕ → ValuePair,
      (∀ n, G.ViscositySolution n (Vn n) ∧
        ∀ U : ValuePair, G.ViscositySolution n U → G.SameValues U (Vn n)) ∧
      ∃ κ : ℕ → ℕ, StrictMono κ ∧ ∃ V θ : ValuePair,
        (∀ i, G.MeasurableField (V i)) ∧
        (∀ i s, s ∈ Icc (0 : ℝ) G.h → ∀ x,
          Tendsto (fun k => Vn (κ k) i s x) atTop (𝓝 (V i s x))) ∧
        (∀ i j s, s ∈ Icc (0 : ℝ) G.h → ∀ x,
          Tendsto (fun k => D j (Vn (κ k) i) s x) atTop (𝓝 (D j (V i) s x))) ∧
        (∀ i, G.Feedback (θ i) ∧
          (∀ s ∈ Icc (0 : ℝ) G.h, ∀ x, D i (V i) s x ≠ 0 → θ i s x = G.lower) ∧
          (∀ x, IsStronglyProgressive naturalFiltration (G.liftFeedback (θ i) x)) ∧
          ∀ x, G.WeakH2
            (fun k => G.maskedSmooth (κ k) (Vn (κ k) i) (V i) i x)
            (G.maskedThreshold (θ i) (V i) i x)) ∧
        G.IsNash (G.limitFeedback V θ 0) (G.limitFeedback V θ 1) ∧
        ∀ i x, G.cost i x
          (G.liftFeedback (G.limitFeedback V θ 0) x)
          (G.liftFeedback (G.limitFeedback V θ 1) x) = V i 0 x := by sorry

end AuctionDuration.ClearingError.Supplement
