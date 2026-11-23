-- Prove2me | Theorems.Thm_ChenWhitt93_Reflection_Supplement_theorem_5_1
-- name    : ChenWhitt93.Reflection.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:54:41.372804+00:00
-- url     : https://prove2.me/theorems/28ec012a-3e72-41ff-a631-129078770076
-- title:
--   Theorem 5.1 (corrected: σ²_{dj} for the printed c²_{dj} in (5.4)) — FCLT for the cumulative down times of J independent alternating renewal processes
-- statement:
--   Consider $J$ stations, each alternating between up and down periods and starting up. The durations $u_k^j$, $d_k^j$ ($k\ge1$, $1\le j\le J$) do not depend on $n$, are nonnegative and mutually independent, and for each $j$ the up periods are identically distributed with mean $u_j$ and variance $\sigma^2_{uj}\in(0,\infty)$, and the down periods are identically distributed with mean $d_j$ and variance $\sigma^2_{dj}\in(0,\infty)$. Let $D_j(t)$ be the cumulative down time of station $j$ in $[0,t]$, and put
--   $$
--   \nu_j=\frac{u_j}{u_j+d_j},\qquad \lambda_j=\frac{1}{d_j+u_j},\qquad \sigma_j^2=\lambda_j(1-\lambda_jd_j)^2\sigma^2_{dj}+\lambda_j^3d_j^2\sigma^2_{uj}.
--   $$
--   Then, as $n\to\infty$,
--   $$
--   \Big(\frac{1}{\sqrt n}\big[D_j(nt)-(1-\nu_j)nt\big]\Big)_{1\le j\le J}\ \Rightarrow\ (\sigma_1W_1(t),\dots,\sigma_JW_J(t))\quad\text{in }D([0,\infty),\mathbb R^J,J_1),
--   $$
--   where $W_1,\dots,W_J$ are independent standard Brownian motions. In the paper's terms: (5.3) holds with $\nu_j=u_j/(u_j+d_j)$ and $c_{\nu j}=0$, and its limit $\hat D$ consists of $J$ independent zero-mean Brownian motions with variance constants $\sigma_j^2$.
--
--   This supplies the down-time FCLT (5.3) with an explicit variance and $c_\nu=0$. Theorem 5.2 additionally assumes joint convergence with the other network primitives.
--
--   **Formalization Note** The limit is continuous, so $J_1$ convergence is uniform convergence on compact sets, and weak convergence is written in coupling (Skorohod-representation) form. The statement is made for every probability space carrying independent standard Brownian motions $W$.
--
--   Differences from the source:
--   - correction: (5.4) σⱼ² = λⱼ(1 − λⱼdⱼ)²c²_{dj} + λⱼ³dⱼ²σ²_{uj} → σⱼ² = λⱼ(1 − λⱼdⱼ)²σ²_{dj} + λⱼ³dⱼ²σ²_{uj} (downVarConst); reason: the proof's (5.9), p. 356, has σ²_{dj}; c²_{dj} is defined nowhere in the paper (c's are drift constants), and σ²_{dj} gives the classical alternating-renewal constant (u²σ²_d + d²σ²_u)/(u + d)³
--   - encoding: weak convergence in D([0, ∞), ℝᴶ, J₁) to a continuous limit → CouplingConverges UocTendsto (Skorohod-representation form, u.o.c. convergence); reason: J₁ convergence to a continuous path is u.o.c. convergence, and on these Polish spaces the coupling form is equivalent to weak convergence
--   - encoding: D̂ composed of J independent zero-mean Brownian motions with variance σⱼ² → D̂ = (σ₁W₁, …, σ_JW_J) for every family W of independent standard Brownian motions (IsIndepStdBrownian); reason: a Brownian motion with variance σⱼ² is σⱼ times a standard one; the finite-dimensional characterization fixes the law, so quantifying over all such W is the same claim
--   - encoding: u_kʲ, d_kʲ, k ≥ 1, random variables → up j k, down j k, k ≥ 0, measurable, nonnegative for every ω; reason: index shift of the published Interruptions; nonnegativity is the Section 3 model; random variables are measurable
--   - generalization: a network of J stations → J : ℕ also permits the empty network J = 0; reason: for J > 0 the full source claim is unchanged; for J = 0 all station vectors are empty and each convergence conclusion is immediate
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), p. 355, Theorem 5.1 (with (5.9), p. 356)

import Mathlib
import Definitions.Def_ChenWhitt93_JumpDiffusion_M1
import Definitions.Def_ChenWhitt93_Reflection_Supplement_AltRenewal

namespace ChenWhitt93.Reflection.Supplement

open MeasureTheory ProbabilityTheory Filter Topology
open ChenWhitt93.JumpDiffusion

/-- Theorem 5.1 (p. 355): in the alternating-renewal-process context, with up/down durations
independent of `n`, `n^{-1/2}[D(nt) − (1 − ν)nt] ⇒ D̂` in `D([0, ∞), ℝᴶ)` (that is, (5.3) with
`νⱼ = uⱼ/(uⱼ + dⱼ)` and `c_{νj} = 0`), where `D̂ = (σ₁W₁, …, σ_JW_J)` for independent standard
Brownian motions `Wⱼ` and `σⱼ² = λⱼ(1 − λⱼdⱼ)²σ²_{dj} + λⱼ³dⱼ²σ²_{uj}`, `λⱼ = 1/(dⱼ + uⱼ)` (the page
prints `c²_{dj}` for `σ²_{dj}` in (5.4); (5.9) of the proof has `σ²_{dj}`). The limit is continuous,
so `J₁` convergence is uniform convergence on compacts; weak convergence is in coupling form, and
the statement holds for every family of independent standard Brownian motions. -/
theorem theorem_5_1 {J : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Pr' : Measure Ω') [IsProbabilityMeasure Pr']
    (I : Ω → Interruptions J) (u d varU varD : Fin J → ℝ)
    (hI : IsAltRenewal Pr I u d varU varD)
    (W : Ω' → ℝ → Fin J → ℝ) (hW : IsIndepStdBrownian Pr' W) :
    CouplingConverges UocTendsto Pr (fun n ω => centredDown (I ω) (upFraction u d) n) Pr'
      (fun ω' t j => if t < 0 then 0 else Real.sqrt (downVarConst u d varU varD j) * W ω' t j) := by sorry

end ChenWhitt93.Reflection.Supplement
