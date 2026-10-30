-- Prove2me | Theorems.Thm_CrossLayerControl_ECCA_theorem_6_3_ecca_performance
-- name    : CrossLayerControl.ECCA.theorem_6_3_ecca_performance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:41:50.82369+00:00
-- url     : https://prove2.me/theorems/b7567279-22a6-4681-9f3f-e0a2f1cd2758
-- title:
--   Theorem 6.3 (ECCA Performance) (corrected: no beneficial cross-coupling of rates; $U(0)\le V+\hat R$)
-- statement:
--   Consider the downlink of §6.3.1 under the standing hypotheses: signs, the rate bound (3.4), the $\beta$-condition $C_i(P,s)\le C_i(P[i],s)+\beta P_i$ and cross-monotonicity $C_j(P,s)\le C_j(P[i],s)$ ($j\ne i$) at feasible power vectors. Let $V>0$ and let the initial backlogs satisfy $0\le U_i(0)\le V+\hat R$. Then:
--
--   **(a) Deterministic bounds.** For every arrival sequence with $0\le A_i(t)\le\hat R$, every state sequence, and every run of ECCA:
--
--   1. $U_i(t)\le U_{max}=V+\hat R$ for all $i$ and $t$;
--   2. $D(t)\le D_{max}=\beta V+\beta\hat R+P_{max}$ for all $t$;
--   3. the energy over any $T$ slots is at most $P_{av}T+D_{max}$: $\sum_{\tau=t_0}^{t_0+T-1}\sum_iP_i(\tau)\le P_{av}T+D_{max}$;
--   4. the average power constraint holds: $\limsup_{T\to\infty}\frac1T\sum_{\tau<T}\sum_iP_i(\tau)\le P_{av}$.
--
--   **(b) Throughput.** If moreover the rates are measurable, and on a probability space the pair $(A(t),S(t))$ is i.i.d. over slots with law $\mu$ relative to a filtration to which ECCA's decisions are adapted, then
--
--   5. with $B=\tfrac12\big(L(\mu_{max}^2+\hat R^2)+P_{av}^2+P_{max}^2\big)$,
--   $$\liminf_{t\to\infty}\frac1t\sum_{\tau=0}^{t-1}\sum_{i=1}^L\mathbb E\{R_i(\tau)\}\ge\sum_ir_i^*-\frac BV,$$
--   where $\sum_ir_i^*$ is the optimal throughput (the closure benchmark of stationary randomized decisions);
--   6. for every admissible policy $(R',P')$ on the same space,
--   $$\liminf_{t\to\infty}\frac1t\sum_{\tau<t}\sum_i\mathbb E\{R_i(\tau)\}\ge\limsup_{t\to\infty}\frac1t\sum_{\tau<t}\sum_i\mathbb E\{R'_i(\tau)\}-\frac BV.$$
--
--   ECCA keeps every queue deterministically bounded by $O(V)$, meets the average power constraint on every sample path, and achieves throughput within $B/V$ of optimal: the $[O(1/V),O(V)]$ utility–backlog trade-off of drift-plus-penalty control.
--
--   Differences from the source:
--   - correction: β-condition only → β-condition plus cross-monotonicity C_j(P,s) ≤ C_j(P[i],s) for j ≠ i (DownlinkHyp); reason: the printed claim is false: L = 2, Pmax = 1, Pav = 0.5, β = 0.01, V = 10, R̂ = 1, µmax = 1, C_1 ≡ 0, C_2(P) = 1[P_1 ≥ 1], A ≡ (0,1) satisfies every printed assumption, ECCA allocates P = (1,0) with D(t) > βU_1(t), and D(t) reaches 10 > βV + βR̂ + Pmax = 1.11
--   - correction: U(0) unstated → 0 ≤ U_i(0) ≤ V + R̂; reason: with U_i(0) = V + R̂ + 1 the bound U_i(t) ≤ V + R̂ fails at t = 0
--   - reading: B a constant computable from the Lyapunov drift → B = (L(µmax² + R̂²) + Pav² + Pmax²)/2, fixed before V; reason: the constant of the drift bound (6.11) for the downlink
--   - reading: Σ_i r*_i, the optimal throughput over all possible policies → rStar (closure benchmark of stationary randomized decisions), plus clause 6 comparing directly with every admissible policy; reason: the paper gives no formula; clause 6 and the converse milestone make the optimality explicit
--   - generalization: all possible policies → admissible policies: measurable, mean-rate stable, average power ≤ Pav, possibly non-causal; reason: contains the paper's strongly stable policies (Lemma 3.3)
--   - reading: A(t) and S(t) i.i.d. over timeslots → (A(t), S(t)) i.i.d. relative to a filtration to which ECCA's decisions are adapted (IsAdaptedIID); reason: for the natural filtration it is the paper's assumption; ECCA's decisions use only current and past information
--   - generalization: ECCA with the rule admit everything iff U_i(t) ≤ V and a maximizer of (6.14) → any minimizer of the flow-control objective and any maximizer of (6.14) (IsECCARun); reason: ties broken arbitrarily; the paper's run is one of these
--   - generalization: Pav < Pmax; topology state set finite (p. 27) → Pav < Pmax not assumed; state space an arbitrary type; reason: no step uses them; the source's setting is a special case
--   - reading: signs of Pav, Pmax, R̂ unstated → 0 ≤ Pav, 0 ≤ Pmax, 0 ≤ R̂ (RateHyp); reason: a negative average power budget is unsatisfiable; R̂ ≥ 0 is forced by 0 ≤ A_i ≤ R̂ when L ≥ 1 and keeps L = 0 nondegenerate; Pmax ≥ 0 follows from 0 ≤ Pav < Pmax
--   - reading: the average power constraint clearly holds → limsup_{T→∞} (1/T) Σ_{τ<T} Σ_i P_i(τ) ≤ Pav on every sample path; reason: the time-average power constraint of §6.3.1
--   - encoding: expectations of the rates; liminf and limsup → measurable rate function (DownlinkMeas); liminf and limsup in EReal; reason: Lean integrals of non-measurable functions are 0; EReal avoids junk limits
--   - encoding: power vectors with Σ P_i ≤ Pmax → power vectors with P_i ≥ 0 and Σ P_i ≤ Pmax; reason: power is nonnegative; the page leaves it implicit
--   - encoding: A_i(t) ≤ R̂ → 0 ≤ A_i(t) ≤ R̂; reason: arrivals are amounts of data, hence nonnegative; with A_i(t) < 0 the flow-control constraint 0 ≤ R_i(t) ≤ A_i(t) is infeasible and no ECCA run (or admissible decision) exists, so no instance is excluded
--   - encoding: links 1,…,L → Fin L (0-based); reason: Lean convention; same instances
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, Theorem 6.3, p. 115; ECCA and (6.13)–(6.14), p. 114; §6.3.1, p. 113; (3.4), p. 27

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_DownlinkHyp
import Definitions.Def_CrossLayerControl_ECCA_DownlinkMeas
import Definitions.Def_CrossLayerControl_ECCA_queueU
import Definitions.Def_CrossLayerControl_ECCA_virtD
import Definitions.Def_CrossLayerControl_ECCA_IsECCARun
import Definitions.Def_CrossLayerControl_ECCA_IsAdaptedIID
import Definitions.Def_CrossLayerControl_ECCA_throughputAvg
import Definitions.Def_CrossLayerControl_ECCA_IsAdmissiblePolicy
import Definitions.Def_CrossLayerControl_ECCA_rStar
import Definitions.Def_CrossLayerControl_ECCA_B

open MeasureTheory Filter

universe u

namespace CrossLayerControl.ECCA

/-- **Theorem 6.3 (ECCA Performance).**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), Theorem 6.3, p. 115: "(ECCA Performance [116]) For any topology
state process S(t) and any input process A(t) that satisfies Ai(t) ≤ R̂ for all t, the ECCA
algorithm ensures: Ui(t) ≤ Umax ≜ V + R̂ for all i and all t, D(t) ≤ Dmax ≜ βV + βR̂ + Pmax for all
t. Consequently, the energy expended over any interval of T slots is never more than PavT + Dmax
(and so the average power constraint clearly holds). Further, if the arrival vector A(t) and
topology state S(t) is i.i.d. over timeslots, then achieved throughput satisfies:
liminf_{t→∞} (1/t) Σ_{τ=0}^{t−1} Σ_{i=1}^L E{Ri(τ)} ≥ Σ_i r∗i − B/V, where Σ_i r∗i is the optimal
throughput over all possible policies, and B is a constant that can be computed from the Lyapunov
drift of the system [116]."

Assume the standing hypotheses `DownlinkHyp M`, a control parameter `V > 0`, and initial backlogs
`0 ≤ Uᵢ(0) ≤ V + R̂`. Then:

(a) For every deterministic arrival sequence with `0 ≤ aᵢ(t) ≤ R̂`, every state sequence, and every
ECCA run `(r, p)`:
1. `Uᵢ(t) ≤ V + R̂` for all `i`, `t`;
2. `D(t) ≤ βV + βR̂ + Pmax` for all `t`;
3. `Σ_{τ=t₀}^{t₀+T−1} Σᵢ Pᵢ(τ) ≤ Pav·T + (βV + βR̂ + Pmax)` for every `t₀`, `T`;
4. `limsup_{T→∞} (1/T) Σ_{τ<T} Σᵢ Pᵢ(τ) ≤ Pav`.

(b) If moreover the rates are measurable (`DownlinkMeas M`), then on every probability space with a
filtration `ℱ`, for arrivals `0 ≤ Aᵢ(t) ≤ R̂` and states `S(t)` whose pair is i.i.d. with law `μ`
relative to `ℱ`, and `ℱ`-adapted decisions `R`, `P` forming an ECCA run on every sample path:
5. `liminf_{t→∞} (1/t) Σ_{τ<t} Σᵢ E Rᵢ(τ) ≥ Σᵢ r∗ᵢ − B/V`, with `Σᵢ r∗ᵢ = rStar M μ` and
   `B = (L(µmax² + R̂²) + Pav² + Pmax²)/2`;
6. for every admissible policy `(R', P')` on the same space (any initial backlog),
   `liminf_{t→∞} (1/t) Σ_{τ<t} Σᵢ E Rᵢ(τ) ≥ limsup_{t→∞} (1/t) Σ_{τ<t} Σᵢ E R'ᵢ(τ) − B/V`.

**Formalization Note.** Corrections: C1 (cross-monotonicity, in `DownlinkHyp`) and C2
(`Uᵢ(0) ≤ V + R̂`); without either the deterministic clauses are false. B is an explicit function
of the model data and does not depend on `V`. ECCA is a relation, so every tie-breaking is covered.
All `liminf`/`limsup` are taken in `EReal`, so none is a junk value. The i.i.d. hypothesis is
stated relative to a filtration to which the decisions are adapted (`IsAdaptedIID`). -/
theorem theorem_6_3_ecca_performance {L : ℕ} {𝒮 : Type*} [MeasurableSpace 𝒮]
    (M : Downlink L 𝒮) (hM : DownlinkHyp M) (V : ℝ) (hV : 0 < V)
    (u₀ : Fin L → ℝ) (hu₀ : ∀ i, 0 ≤ u₀ i ∧ u₀ i ≤ V + M.Rhat) :
    (∀ (a : ℕ → Fin L → ℝ) (s : ℕ → 𝒮) (r p : ℕ → Fin L → ℝ),
      (∀ t i, 0 ≤ a t i ∧ a t i ≤ M.Rhat) → IsECCARun M V u₀ a s r p →
      (∀ t i, queueU M u₀ s r p t i ≤ V + M.Rhat) ∧
      (∀ t, virtD M p t ≤ M.β * V + M.β * M.Rhat + M.Pmax) ∧
      (∀ t₀ T : ℕ, ∑ τ ∈ Finset.Ico t₀ (t₀ + T), ∑ i, p τ i ≤
        M.Pav * T + (M.β * V + M.β * M.Rhat + M.Pmax)) ∧
      limsup (fun T : ℕ => (((T : ℝ)⁻¹ * ∑ τ ∈ Finset.range T, ∑ i, p τ i : ℝ) : EReal))
        atTop ≤ (M.Pav : EReal)) ∧
    (DownlinkMeas M →
      ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
        (ℱ : Filtration ℕ mΩ) (A : ℕ → Ω → Fin L → ℝ) (S : ℕ → Ω → 𝒮)
        (R P : ℕ → Ω → Fin L → ℝ) (μ : Measure ((Fin L → ℝ) × 𝒮)),
        IsAdaptedIID Pr ℱ A S μ →
        (∀ t ω i, 0 ≤ A t ω i ∧ A t ω i ≤ M.Rhat) →
        (∀ t, Measurable[ℱ t] (R t) ∧ Measurable[ℱ t] (P t)) →
        (∀ ω, IsECCARun M V u₀ (fun t => A t ω) (fun t => S t ω) (fun t => R t ω)
          (fun t => P t ω)) →
        ((rStar M μ - B M / V : ℝ) : EReal) ≤
            liminf (fun t : ℕ => (throughputAvg Pr R t : EReal)) atTop ∧
        ∀ (R' P' : ℕ → Ω → Fin L → ℝ) (u₀' : Fin L → ℝ),
          IsAdmissiblePolicy M Pr A S R' P' u₀' →
          limsup (fun t : ℕ => (throughputAvg Pr R' t : EReal)) atTop - ((B M / V : ℝ) : EReal) ≤
            liminf (fun t : ℕ => (throughputAvg Pr R t : EReal)) atTop) := by sorry

end CrossLayerControl.ECCA
