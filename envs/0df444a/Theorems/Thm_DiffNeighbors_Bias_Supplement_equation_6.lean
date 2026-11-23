-- Prove2me | Theorems.Thm_DiffNeighbors_Bias_Supplement_equation_6
-- name    : DiffNeighbors.Bias.Supplement.equation_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:14:05.741404+00:00
-- url     : https://prove2.me/theorems/4e9b20e2-d445-4b0c-92f7-9bb5e8d27b5a
-- title:
--   Equation (6) (corrected: absolute value) — the unit mixed difference is bounded by Lδ²
-- statement:
--   Let $I$ be a finite unit set, $G$ an undirected graph without self-loops, and $f_i:\{0,1\}^I\to\mathbb R$ the potential outcomes. Write $f_i^a(z)=f_i(z^{z_i=a})$ and let $\mathcal N_i$ denote its neighbours. Suppose $\delta>0$ and $f_i^a(z)=g_i^a(\delta z)$, with $g_i^a$ twice differentiable within $[0,\delta]^I$ and all mixed second derivatives for distinct neighbours bounded in absolute value by $L$ (Assumption 2).
--
--   For every unit $i$, binary treatment $a$, treatment vector $z$, and distinct neighbours $j,k\in\mathcal N_i$,
--   $$|\Delta_{jk}f_i^a(z)|\le L\delta^2.$$
--   Here $\Delta_{jk}h(z)=h(z^{1,1})-h(z^{0,1})-h(z^{1,0})+h(z^{0,0})$, changing only entries $j,k$. This is Lemma 1's unit-level base case. Neighborhood interference is unnecessary.
--
--   Differences from the source:
--   - correction: Equation (6) first equates the signed Δ_jk f_i^a to its absolute value → the conclusion bounds |Δ_jk f_i^a| by Lδ²; reason: the equality is false on the three-node star with f_0^a(z)=-z_1z_2, δ=L=1: the signed difference is -1 and its absolute value is 1; the intended absolute bound is used on p. 29
--   - reading: scaled functions and second derivatives on the box in §2.2 and Assumption 2 → functions on all unit coordinates, parameterized at δz, twice differentiable within [0,δ]^I with bounded mixed within-derivatives only for distinct neighbours; reason: neighbour functions compose with the projection; p. 6 specifies the box and presupposes these derivatives exist, with no global regularity requirement
--   - reading: Equation (6) says any j,k in N_i while invoking Assumption 2 → j and k are distinct neighbours; reason: Assumption 2 bounds distinct mixed partials; repeated-index signed differences vanish by the published definition
--   - generalization: Assumption 1 holds throughout the paper → neighborhood interference is omitted for this local finite-difference bound; reason: only the parameterization and mixed derivative bounds are used; every neighborhood-interference model remains an instance
--   - encoding: binary treatment vectors on [N] → Bool-valued vectors on finite types, with the published conditional outcome and signed finite difference; reason: Bool encodes zero and one and all finite source instances are retained
-- source:
--   Peng, Ye, Zheng, Differences-in-Neighbors for Network Interference in Experiments, arXiv:2503.02271v1, p. 9, Equation (6), proof of Corollary 1; pp. 5–6, §2.2 and Assumption 2

import Mathlib
import Definitions.Def_DiffNeighbors_Bias_Supplement_SmoothModel

namespace DiffNeighbors.Bias.Supplement

/-- Equation (6), p. 9: the mixed finite-difference bound under Assumption 2.
Only distinct neighbours are constrained by Assumption 2. Neighborhood
interference is unnecessary for this local assertion and is omitted. -/
theorem equation_6 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (f : ι → (ι → Bool) → ℝ)
    (g : ι → Bool → (ι → ℝ) → ℝ) (δ L : ℝ) (hδ : 0 < δ)
    (hg : SmoothInterference G f g δ L)
    (i : ι) (a : Bool) (z : ι → Bool) (j k : ι)
    (hj : G.Adj i j) (hk : G.Adj i k) (hjk : j ≠ k) :
    |secondDiff (condOutcome f i a) j k z| ≤ L * δ ^ 2 := by sorry

end DiffNeighbors.Bias.Supplement
