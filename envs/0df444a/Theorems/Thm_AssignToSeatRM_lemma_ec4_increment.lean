-- Prove2me | Theorems.Thm_AssignToSeatRM_lemma_ec4_increment
-- name    : AssignToSeatRM.lemma_ec4_increment
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:27:44.966586+00:00
-- url     : https://prove2.me/theorems/a15deb12-500d-456c-9957-075f6a6808db
-- title:
--   Lemma EC.4 — each increment of the loss decomposition lies in $[0,2l]$ with $l$ depending only on the prices
-- statement:
--   Fix the number of legs $M$ and prices $p_{ij}\ge0$. There is $l>0$, depending only on these, such that for every horizon $T$, every initial vector of maximal-sequence counts $A^1$, every decision path feasible on $[1,T]$ and every $t\in[1,T]$,
--
--   $$0\ \le\ \mathrm{OPT}\big(A^1,d^{[1,T]},\gamma^{[1,t)}\big)-\mathrm{OPT}\big(A^1,d^{[1,T]},\gamma^{[1,t+1)}\big)\ \le\ 2l.$$
--
--   The difference is the loss incurred by committing to the decision of period $t$ when the rest of the demand is known; it is never negative because one more lower bound shrinks the feasible set, and it is uniformly bounded because each period carries at most one request. Summed over $t$ it is the loss of the path against the hindsight optimum (EC.19).
--
--   Differences from the source:
--   - generalization: the sample path of RDP from A¹ = f(C¹) → every decision path feasible on [1,T] (each period at most one request; each allocation into a maximal sequence with A^t_{uv} ≥ 1; counts updated by (8)) from every A¹ ∈ ℕ^{u ≤ v}; reason: RDP's path is such a path (constraints (15) give A^t_{uv} ≥ 1 for the chosen [u,v]) and A¹ = f(C¹) is a natural-number vector, so the statement specializes to the source's; the source's proof uses only these properties
--   - encoding: (u^t, i^t, j^t, v^t) for each period, γ^{[t1,t2)}, d^{[t1,t2)}, A^t → dec : ℕ → Option (ℕ⁴) with none = no request and (0,i,j,0) = rejection; gammaCount, demandCount count periods in [t1,t2); msState gives A^t; reason: Lean convention; same paths
--   - encoding: l > 0 'only dependent on {p_{ij}}' → ∃ l > 0 after M and p, before T, A¹, the path and t; reason: the prices determine M; same quantifier order
--   - reading: prices p_{ij} of the model, sign not restated in the result → p_{ij} ≥ 0 for every itinerary (IsPriceVec); reason: reading R1: the prices are fares (p.8) and Theorem 2 speaks of positive prices; the model does not admit negative fares
--   - encoding: the optimal value of a linear program → sSup of the objective over the feasible set; reason: the feasible sets that occur are nonempty and bounded, so the sSup is the maximum; same values
--   - encoding: the variables γ_{uijv} (u ≤ i ≤ j ≤ v) and γ_{0ij0} of (14)/(EC.18) → γ : ℕ×ℕ×ℕ×ℕ → ℝ, required to vanish outside the index set gammaIdx M; the reject variable is γ(0,i,j,0); reason: the other coordinates are not variables of the LP; fixing them to 0 changes no feasible objective value
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, Lemma EC.4, p.ec19; proof pp.ec19–ec21

import Mathlib
import Definitions.Def_AssignToSeatRM_Basic
import Definitions.Def_AssignToSeatRM_DynamicPrimal
import Definitions.Def_AssignToSeatRM_DecisionPath
import Definitions.Def_AssignToSeatRM_Dynamic

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace AssignToSeatRM

/-- **Lemma EC.4** (Zhu, Liu, Wang and Wang, *Assign-to-Seat*, MSOM 2023,
doi:10.1287/msom.2023.1188, p.ec19): there exists some `l > 0` only dependent on `{p_{ij}}` such
that `0 ≤ OPT(A¹, d^{[1,T]}, γ^{[1,t)}) − OPT(A¹, d^{[1,T]}, γ^{[1,t+1)}) ≤ 2l` for any `A¹`,
`d^{[1,T]}` and `t ∈ [1, T]`.

**Formalization Note.** `l` is chosen after the number of legs `M` and the prices `p ≥ 0` and
before everything else: it works for every horizon `T`, every `A¹ ∈ ℕ^{u ≤ v}` and every decision
path feasible on `[1, T]` (RDP's path is one). `d^{[1,T]} = d^{[1,T+1)}`. -/
theorem lemma_ec4_increment (M : ℕ) (p : ℕ → ℕ → ℝ) (hp : IsPriceVec M p) :
    ∃ l : ℝ, 0 < l ∧
      ∀ (T : ℕ) (A₁ : ℕ → ℕ → ℕ) (dec : ℕ → Option Idx4), IsFeasPath M T A₁ dec →
        ∀ t ∈ Finset.Icc 1 T,
          0 ≤ OPT M p (fun u v => (A₁ u v : ℝ))
                (fun i j => (demandCount dec 1 (T + 1) i j : ℝ))
                (fun c => (gammaCount dec 1 t c : ℝ)) -
              OPT M p (fun u v => (A₁ u v : ℝ))
                (fun i j => (demandCount dec 1 (T + 1) i j : ℝ))
                (fun c => (gammaCount dec 1 (t + 1) c : ℝ)) ∧
          OPT M p (fun u v => (A₁ u v : ℝ))
                (fun i j => (demandCount dec 1 (T + 1) i j : ℝ))
                (fun c => (gammaCount dec 1 t c : ℝ)) -
              OPT M p (fun u v => (A₁ u v : ℝ))
                (fun i j => (demandCount dec 1 (T + 1) i j : ℝ))
                (fun c => (gammaCount dec 1 (t + 1) c : ℝ)) ≤ 2 * l := by sorry

end AssignToSeatRM
