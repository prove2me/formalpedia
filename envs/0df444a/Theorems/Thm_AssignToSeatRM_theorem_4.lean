-- Prove2me | Theorems.Thm_AssignToSeatRM_theorem_4
-- name    : AssignToSeatRM.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:27:45.372686+00:00
-- url     : https://prove2.me/theorems/e6c5708b-e303-4b68-81fc-707cd2ccdce9
-- title:
--   Theorem 4 — RDP loses $O(\sqrt\theta)$ against the hindsight optimum, and $O(1)$ under NEE
-- statement:
--   Let $I=\langle C,\{p_{ij}\}_{i\le j},\{\lambda^t_{ij}\}_{i\le j,\,t\in[T]}\rangle$ be any instance: a capacity matrix $C\in\{0,1\}^{N\times M}$, prices $p_{ij}\ge0$, and arrival probabilities $\lambda^t_{ij}\ge0$ with $\sum_{i\le j}\lambda^t_{ij}\le1$ for every period. In the $\theta$-th problem the seats are copied $\theta$ times and the horizon is stretched to $\theta T$. Then:
--
--   1. there is a constant $K$, depending only on $I$, such that for every $\theta\ge1$ and every RDP policy $\pi$,
--   $$V^{HO}_\theta(I)-V^{\pi}_\theta(I)\ \le\ K\sqrt\theta;$$
--   2. if the arrival probabilities satisfy NEE (every itinerary that can arrive can also arrive in the last period $T$), there is $K$, depending only on $I$, such that for every $\theta\ge1$ and every RDP policy $\pi$,
--   $$V^{HO}_\theta(I)-V^{\pi}_\theta(I)\ \le\ K.$$
--
--   $V^{HO}_\theta$ is the expected optimal value of the seat-level LP relaxation (2) on the realized demand (the hindsight optimum) and $V^\pi_\theta$ the expected revenue of $\pi$. An RDP policy (Algorithm 3) re-solves, in every period $t$ after seeing the request $i^t\to j^t$, the dynamic primal (14) with $A=f(C^t)$ and the expected remaining demand $\lambda^{[t,\theta T]}$ under the constraints (15), and puts the request into a maximal-sequence type $[u,v]$ that maximizes $\gamma_{ui^tj^tv}$ (or rejects it if the rejection coordinate is maximal).
--
--   This is the paper's main result: re-solving an LP whose size depends only on the number of legs gives a policy whose loss against the full-information benchmark grows at most like $\sqrt\theta$, and stays bounded when all ticket sales can continue to the end; Proposition 1 shows that the $\sqrt\theta$ rate cannot be improved without NEE.
--
--   **Formalization Note** "Every RDP policy" means every deterministic non-anticipating policy that, at every history of positive probability, makes a decision RDP can make for some optimal solution of (14)+(15) and some tie-break; a proved sanity check exhibits such a policy for every instance and $\theta\ge1$.
--
--   Differences from the source:
--   - reading: prices p_{ij} of the model, sign not restated in the result → p_{ij} ≥ 0 for every itinerary (IsPriceVec); reason: reading R1: the prices are fares (p.8) and Theorem 2 speaks of positive prices; the model does not admit negative fares
--   - reading: V^HO_θ(I) − V^RDP_θ(I) = O(√θ) (resp. O(1)), with RDP taking 'an optimal solution' and 'Break ties arbitrarily' → ∃ K ∀ θ ≥ 1 ∀ π RDP-consistent, V^HO_θ − V^π_θ ≤ K√θ (resp. ≤ K under NEE); reason: reading R2: RDP is a family of policies (any optimal solution, any tie-break, any seat of M_{u^t v^t}(C^t)); the stronger, uniform reading is taken, and the proof's constants depend only on I
--   - reading: RDP's rule in every period → required only at histories of positive probability; reason: reading R3: on a null history RDP's choice may be undefined (all optimal γ may vanish and M_{uv}(C^t) be empty); null histories do not enter any expectation
--   - generalization: RDP's arbitrary tie-breaking and seat choice → the tie-break and the seat may depend on the whole history of requests (deterministic, non-anticipating); reason: every RDP policy whose choices depend on (t, C^t) and the request is included
--   - encoding: NEE: inf_{i≤j: λ^{[1,T]}_{ij} > 0} λ^T_{ij} > 0 → every itinerary with Σ_{t∈[T]} λ^t_{ij} > 0 has λ^T_{ij} > 0; reason: the infimum over a finite set is a minimum; the implication avoids Lean's sInf ∅ = 0
--   - encoding: θ ∈ ℕ, C(θ)_{(k+(s−1)N)ℓ} = C_{kℓ}, λ^t(θ) = λ^{⌈t/θ⌉} → θ ≥ 1; seat m of C(θ) copies seat m mod N; lam ((t + θ − 1)/θ); reason: Lean convention; same instances
--   - encoding: expected revenue over the random requests → finite sum over request sequences ω : Fin (θT) → Option itinerary weighted by Π_t q_t(ω_t); reason: the product law is the law of independent arrivals across periods; same expectations
--   - encoding: a policy assigns only seats that are free → a decision naming a seat that is not free counts as a rejection; reason: RDP-consistent policies always name a free seat of M_{u^t v^t}(C^t); same policies
--   - encoding: legs 1..M, itineraries i ≤ j, C ∈ {0,1}^{N×M} with C_{k0} = C_{k(M+1)} = 0 → natural-number indices with explicit bounds (itins M); C : Fin N → Fin M → Bool read through cap, which is false outside 1..M; reason: Lean convention; same instances
--   - encoding: the optimal value of a linear program → sSup of the objective over the feasible set; reason: the feasible sets that occur are nonempty and bounded, so the sSup is the maximum; same values
--   - encoding: the variables γ_{uijv} (u ≤ i ≤ j ≤ v) and γ_{0ij0} of (14)/(EC.18) → γ : ℕ×ℕ×ℕ×ℕ → ℝ, required to vanish outside the index set gammaIdx M; the reject variable is γ(0,i,j,0); reason: the other coordinates are not variables of the LP; fixing them to 0 changes no feasible objective value
--   - generalization: N, M, T ≥ 1 (implicit in the model) → any N, M, T ∈ ℕ; reason: at N = 0, M = 0 or T = 0 no request can be accepted and both values are 0; the source's instances are all included
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, Theorem 4, p.21; Algorithm 3 and Definition 3, p.20; §4 pp.13–14

import Mathlib
import Definitions.Def_AssignToSeatRM_Basic
import Definitions.Def_AssignToSeatRM_StaticLP
import Definitions.Def_AssignToSeatRM_DynamicPrimal
import Definitions.Def_AssignToSeatRM_Dynamic

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace AssignToSeatRM

/-- **Theorem 4** (Zhu, Liu, Wang and Wang, *Assign-to-Seat*, MSOM 2023,
doi:10.1287/msom.2023.1188, p.21): for any `I = ⟨C, {p_{ij}}_{i ≤ j}, {λ^t_{ij}}_{i ≤ j, t ∈ [T]}⟩`,
`V^HO_θ(I) − V^RDP_θ(I) = O(√θ)`. Furthermore, if `{λ^t_{ij}}` satisfies the NEE property, then
`V^HO_θ(I) − V^RDP_θ(I) = O(1)`.

**Formalization Note.**
1. The instance is arbitrary: any `N, M, T`, any `C ∈ {0,1}^{N×M}`, prices `p_{ij} ≥ 0`, arrival
   probabilities with `λ^t_{ij} ≥ 0` and `Σ_{i ≤ j} λ^t_{ij} ≤ 1`.
2. `V^RDP_θ` is the expected revenue `V^π_θ` of any policy `π` that RDP (Algorithm 3) can
   produce (`IsRDP`: any optimal solution of (14)+(15), any tie-break, any seat in
   `M_{uᵗvᵗ}(Cᵗ)`, at every history of positive probability).
3. `O(·)` is uniform: the constant `K` depends only on the instance, and the bound holds for
   every `θ ≥ 1` and every such `π`.
4. `V^HO_θ` is the expected optimal value of the static LP (2) for `C(θ)` and the realized
   demand of the θ-th problem. -/
theorem theorem_4 {N M T : ℕ} (C : CapMat N M) (p : ℕ → ℕ → ℝ) (lam : ℕ → ℕ → ℕ → ℝ)
    (hp : IsPriceVec M p) (hlam : IsArrivalProb M T lam) :
    (∃ K : ℝ, ∀ θ : ℕ, 1 ≤ θ → ∀ π : Policy (θ * T) M (θ * N), IsRDP C p lam θ T π →
        VHO C p lam θ T - Vpol C p lam θ T π ≤ K * Real.sqrt θ) ∧
      (IsNEE M T lam → ∃ K : ℝ, ∀ θ : ℕ, 1 ≤ θ → ∀ π : Policy (θ * T) M (θ * N),
        IsRDP C p lam θ T π → VHO C p lam θ T - Vpol C p lam θ T π ≤ K) := by sorry

end AssignToSeatRM
