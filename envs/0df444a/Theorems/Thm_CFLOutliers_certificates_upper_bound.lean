-- Prove2me | Theorems.Thm_CFLOutliers_certificates_upper_bound
-- name    : CFLOutliers.certificates_upper_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:39:00.142492+00:00
-- url     : https://prove2.me/theorems/af782aaa-53f8-4098-9c7d-bcde8d7ca2e7
-- title:
--   §3.1, (9)–(10) — the open and close certificates upper-bound the potential change
-- statement:
--   Let the instance satisfy the standing assumptions, let $\lambda\ge 0$, and let $S$ be a capacity-feasible solution. Write $\Phi^*_\lambda(F')$ for the potential of the open set $F'$ with an optimal penalty assignment. Then
--
--   1. for every admissible open operation $\mathrm{open}(t,K)$,
--   $$\Phi^*_\lambda\bigl((F_S\cup\{t\})\setminus K\bigr)\le\Phi_\lambda(S)+\widehat\Delta_{\mathrm{open}}(t,K);$$
--   2. for every admissible close operation $\mathrm{close}(s,T)$ with amounts $a$,
--   $$\Phi^*_\lambda\bigl((F_S\setminus\{s\})\cup T\bigr)\le\Phi_\lambda(S)+\widehat\Delta_{\mathrm{close}}(s,T,a).$$
--
--   Hence every change accepted because its certificate is below $-\tau$ decreases $\Phi_\lambda$ by more than $\tau$, which is what makes the local search terminate and underlies the warm-start relation.
--
--   Differences from the source:
--   - generalization: a finite metric space with distances c → a pseudometric on the index set F ⊔ C (distinct points may be at distance 0); reason: it covers every metric instance, including a facility co-located with a client; no step of the paper uses positivity of distances
--   - reading: "Both certificates upper-bound the actual potential change" → Φ*_λ(new open set) ≤ Φ_λ(S) + certificate, with Φ*_λ the potential under an optimal penalty assignment on the new open set; reason: p.8: "After any change we compute the best penalty assignment under the original capacities", so the actual change is Φ*_λ(new open set) − Φ_λ(S)
--   - generalization: the current solution of the search, whose assignment is optimal → any capacity-feasible solution S; reason: A_t is defined as a change relative to the current assignment and the argument of p.8 and Appendix D does not use optimality; the search state is a special case
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), §3.1, p.8, displays (9)–(10) and the paragraph after them; Appendix D, "Feasibility and assignment values", p.17

import Mathlib
import Definitions.Def_CFLOutliers_assignChange

namespace CFLOutliers

open Finset

/-- **The certificates (9) and (10) upper-bound the potential change**
(Dabas, arXiv:2611.04094, §3.1, p.8: "Both certificates upper-bound the actual potential change";
justified in Appendix D, p.17).

For an instance satisfying the standing assumptions, a penalty `λ ≥ 0` and a capacity-feasible
solution `S`:
1. for every admissible `open(t, K)`, `Φ*_λ((F_S ∪ {t}) \ K) ≤ Φ_λ(S) + Δ̂_open(t, K)`;
2. for every admissible `close(s, T)` with amounts `a`,
   `Φ*_λ((F_S \ {s}) ∪ T) ≤ Φ_λ(S) + Δ̂_close(s, T, a)`.

**Formalization Note.** `Φ*_λ(F')` is the potential of the open set `F'` with an optimal penalty
assignment, the solution the algorithm computes after the change. `S` need not have an optimal
assignment (`A_t` is a change relative to the current assignment). -/
theorem certificates_upper_bound (I : Inst) (hI : I.Std) (lam : ℝ) (hlam : 0 ≤ lam)
    (S : Sol I) (hS : S.CapFeasible) :
    (∀ t K, OpenAdm S t K →
      PhiStar I lam (insert t S.openSet \ K) ≤ Phi lam S + DeltaOpen lam S t K) ∧
    (∀ s T a, CloseAdm S s T a →
      PhiStar I lam (S.openSet.erase s ∪ T) ≤ Phi lam S + DeltaClose lam S s T a) := by sorry

end CFLOutliers
