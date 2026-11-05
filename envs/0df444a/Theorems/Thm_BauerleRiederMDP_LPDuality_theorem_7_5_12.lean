-- Prove2me | Theorems.Thm_BauerleRiederMDP_LPDuality_theorem_7_5_12
-- name    : BauerleRiederMDP.LPDuality.theorem_7_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:31:53.433496+00:00
-- url     : https://prove2.me/theorems/ade1efdd-3cd7-43bb-b377-54d78a660808
-- title:
--   Theorem 7.5.12 — value iteration on a grid approximates $J_\infty$ in $\|\cdot\|_G$
-- statement:
--   Let $E$ be a subset of a real normed space with the Borel $\sigma$-algebra, and $(E,A,D,Q,r,\beta)$ a contracting Markov Decision Model with a bounding function $b$ ($\beta\alpha_b<1$) such that
--
--   1. $b(x)\ge1$ for all $x\in E$;
--   2. $b$ is uniformly continuous on $E$;
--   3. the Structure Assumption (SA) holds for $I\!M_c=\{v\in\mathbb B_b\mid v\text{ uniformly continuous}\}$: $\mathcal Tv\in I\!M_c$ for $v\in I\!M_c$, every $v\in I\!M_c$ has a maximizer, and the limit value function $J=\lim_nJ_n$ lies in $I\!M_c$ with $J=\mathcal TJ$.
--
--   Then the value function $J_\infty$ is real-valued, and for every grid $G\subset E$ with interpolation scheme such that $\beta\alpha_G<1$, every $g\in I\!M_c$ and every $n\in\mathbb N$,
--   $$
--   \|J_\infty-\mathcal T_G^ng\|_G\le\frac{1}{1-\beta\alpha_G}\Big((\beta\alpha_G)^n\|\mathcal T_Gg-g\|_G+\|J_\infty-\mathcal T_GJ_\infty\|_G\Big),
--   $$
--   where $\|J_\infty-\mathcal T_GJ_\infty\|_G\to0$ if the mesh size $h$ of the grid tends to zero.
--
--   So value iteration on a grid, with linear interpolation between grid points, approximates the value function up to an error that vanishes as the grid is refined.
--
--   **Formalization Note** $\|\cdot\|_G$ and $\alpha_G$ take values in $[0,\infty]$ and $1/(1-\beta\alpha_G)$ is an inverse in $[0,\infty]$. The limit statement is asserted for every family of grid schemes, indexed along any filter, whose mesh sizes tend to $0$. In (SA), $\mathcal T$ is the platform's extended-real operator `MDPFinance.LPDuality.T`, $J$ is `Jlim` and $J_\infty$ is `Jinf`.
--
--   Differences from the source:
--   - generalization: E and A Borel spaces, D a Borel subset of E × A, E inside ℝ^d so that x = Σ_k λ_k x_k makes sense → E any subset of a real normed space with the Borel σ-algebra, A any measurable space, D measurable; reason: the Borel-space structure is not used; Borel subsets of ℝ^d are a special case
--   - reading: x = Σ_k λ_k x_k for x ∉ G, with no rule for choosing among several representations → a fixed interpolation scheme (one weight vector per state), and the statement for every such scheme; reason: the book leaves the choice open; quantifying over all schemes is the strongest reading
--   - reading: a (discrete) grid G and the module b_G as a bounding function → G countable and every weight x ↦ λ_y(x) measurable; reason: a discrete grid in a separable space is countable, and measurable weights are what make b_G measurable, as the book asserts
--   - reading: mesh size h of the grid, not defined → h bounds the distance from x to every grid point with positive weight in its representation; reason: this is the property the book's proof of the limit uses (T_G J_∞ = J_∞ on G and uniform continuity of J_∞)
--   - reading: 'if the mesh size h tends to zero' → for every family of grid schemes indexed along any filter whose mesh sizes tend to 0; reason: covers sequences of grids and every other way of refining
--   - encoding: ‖·‖_G, α_G and 1/(1 − βα_G) as real numbers → values in [0, ∞] and (1 − βα_G)⁻¹ in [0, ∞]; reason: avoids the default value of a real supremum of an unbounded set; on finite values they agree
--   - encoding: α_G := sup over (x, a) → supremum over (x, a) ∈ D; reason: Q(·|x, a) is only defined on D in the book
--   - encoding: J_∞ a real function (presupposed by ‖J_∞ − T_G J_∞‖_G) → the conclusion asserts a real J with J_∞ = J (platform J_∞ is extended-real valued); reason: under (SA) J_∞ = J ∈ IM_c by Theorem 7.1.8, so this only names the book's function
--   - encoding: (SA)(iii): a maximizer in some Δ ⊂ F → a maximizer (a measurable decision rule) exists; reason: Δ is existentially quantified in (SA), so it can be taken to be F
--   - encoding: T_G defined on IM_c → T_G defined on all real functions and applied to g ∈ IM_c and its iterates; reason: the formula is the same; only the iterates of g ∈ IM_c enter
--   - encoding: Q a stochastic kernel from D to E and r a measurable function on D → Q a Markov kernel and r a measurable function on E × A (platform MarkovDecisionModel); reason: only the values on D enter any statement; every kernel and reward on D extends to E × A
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 7.5.12, p.222 (PDF 233); setting §7.5.3, p.221 (PDF 232); Structure Assumption (SA), §7.1, p.199 (PDF 210)

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Bounding
import Definitions.Def_MDPFinance_LPDuality_Value
import Definitions.Def_BauerleRiederMDP_LPDuality_bellmanOpReal
import Definitions.Def_BauerleRiederMDP_LPDuality_IMc
import Definitions.Def_BauerleRiederMDP_LPDuality_GridScheme
import Definitions.Def_BauerleRiederMDP_LPDuality_gridBound
import Definitions.Def_BauerleRiederMDP_LPDuality_gridOp
import Definitions.Def_BauerleRiederMDP_LPDuality_normG
import Definitions.Def_BauerleRiederMDP_LPDuality_alphaG

open MeasureTheory ProbabilityTheory Filter Topology MDPFinance.LPDuality

namespace BauerleRiederMDP.LPDuality

/-- **Theorem 7.5.12** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem 7.5.12, p.222, PDF 233; setting §7.5.3, p.221, PDF 232). Suppose that
`βα_G < 1`. Then it holds for `g ∈ IM_c`
`‖J_∞ - T_G^n g‖_G ≤ 1/(1 - βα_G) ((βα_G)^n ‖T_G g - g‖_G + ‖J_∞ - T_G J_∞‖_G)`,
where `‖J_∞ - T_G J_∞‖_G → 0` if the mesh size `h` tends to zero.

Setting of §7.5.3: a contracting model (bounding function `b`, `βα_b < 1`) with (i) `b ≥ 1`,
(ii) `b` uniformly continuous, (iii) the Structure Assumption (SA) (p.199) for
`IM_c = {v ∈ IB_b | v uniformly continuous}`: `0 ∈ IM_c`, `T v ∈ IM_c` for `v ∈ IM_c`, every
`v ∈ IM_c` has a maximizer, and the limit value function `J = lim_n J_n` lies in `IM_c` with
`J = T J`.

The conclusion first asserts that `J_∞` is real-valued (as the book presupposes when it forms
`J_∞ - T_G J_∞`), then the error bound for every grid scheme with `βα_G < 1`, every `g ∈ IM_c` and
every `n`, then the limit statement for every family of grid schemes whose mesh sizes tend to `0`.

**Formalization Note** The state space is a subset `S` of a real normed space `V` (convex
combinations `x = ∑ λ_k x_k` need a linear structure, uniform continuity a metric), with the Borel
σ-algebra on `V` and the subspace σ-algebra on `S`. A grid scheme fixes one interpolation
representation per state (`GridScheme`). The norms `‖·‖_G` and the module `α_G` take values in
`[0, ∞]`, and `1/(1 - βα_G)` is `(1 - βα_G)⁻¹` in `ℝ≥0∞`. `T` in (SA) is the platform's `EReal`
operator `MDPFinance.LPDuality.T`; `T_G` uses the real operator `bellmanOpReal`. "Mesh size `h`
tends to zero" is read along an arbitrary filter on an arbitrary index type. -/
theorem theorem_7_5_12 {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [MeasurableSpace A] {S : Set V}
    (M : MarkovDecisionModel S A) (b : S → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb)
    (hαb : M.β * αb < 1) (hb1 : ∀ x, 1 ≤ b x) (hbuc : UniformContinuous b)
    (hSA_T : ∀ v ∈ IMc b, ∃ w ∈ IMc b, T M (fun x => (v x : EReal)) = fun x => (w x : EReal))
    (hSA_max : ∀ v ∈ IMc b, ∃ f : S → A, IsMaximizerOf M (fun x => (v x : EReal)) f)
    (hSA_J : ∃ w ∈ IMc b, (∀ x, Jlim M x = (w x : EReal)) ∧
      T M (fun x => (w x : EReal)) = fun x => (w x : EReal)) :
    ∃ J : S → ℝ, (∀ x, Jinf M x = (J x : EReal)) ∧
      (∀ (sch : GridScheme S) (g : S → ℝ), g ∈ IMc b →
        ENNReal.ofReal M.β * alphaG M sch b < 1 → ∀ n : ℕ,
          normG sch b (fun x => J x - (gridOp M sch)^[n] g x) ≤
            (1 - ENNReal.ofReal M.β * alphaG M sch b)⁻¹ *
              ((ENNReal.ofReal M.β * alphaG M sch b) ^ n *
                  normG sch b (fun x => gridOp M sch g x - g x) +
                normG sch b (fun x => J x - gridOp M sch J x))) ∧
      (∀ {ι : Type} (l : Filter ι) (sch : ι → GridScheme S),
        Tendsto (fun i => (sch i).h) l (𝓝 0) →
          Tendsto (fun i => normG (sch i) b (fun x => J x - gridOp M (sch i) J x)) l (𝓝 0)) := by sorry

end BauerleRiederMDP.LPDuality
