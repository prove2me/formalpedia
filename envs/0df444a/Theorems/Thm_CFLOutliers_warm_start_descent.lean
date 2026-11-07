-- Prove2me | Theorems.Thm_CFLOutliers_warm_start_descent
-- name    : CFLOutliers.warm_start_descent
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:51.233202+00:00
-- url     : https://prove2.me/theorems/e43f8591-1602-43a7-8ac2-abd19b649cc7
-- title:
--   §2.3 — the warm start cannot increase the potential: $b+\lambda^+(n-q^+)\le a+\lambda^+(n-q^-)$
-- statement:
--   Let the instance satisfy the standing assumptions, $\lambda\ge 0$, $\tau>0$, and let $S_0$ be a capacity-feasible solution. For every run of $\mathrm{Local}(\lambda,\tau;S_0)$ with output $S$,
--
--   $$\Phi_\lambda(S)\le\Phi_\lambda(S_0).$$
--
--   In §2.3 this is applied with $S_0=S^-$ and $\lambda=\lambda^+$: it gives $b+\lambda^+(n-q^+)\le a+\lambda^+(n-q^-)$, that is $b\le a+t$ with $t=\lambda^+(q^+-q^-)$, the second endpoint bound of (6).
--
--   Differences from the source:
--   - generalization: a finite metric space with distances c → a pseudometric on the index set F ⊔ C (distinct points may be at distance 0); reason: it covers every metric instance, including a facility co-located with a client; no step of the paper uses positivity of distances
--   - generalization: the search at penalty λ⁺ started from S⁻ → every run of Local(λ, τ; S₀) for every λ ≥ 0, τ > 0 and every capacity-feasible start S₀; reason: the paper's case is the instance S₀ = S⁻, λ = λ⁺; the argument (reoptimization, then accepted changes that each decrease Φ_λ) uses nothing else
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), §2.3, p.6, the warm-start relation before display (6)

import Mathlib
import Definitions.Def_CFLOutliers_LocalRun

namespace CFLOutliers

/-- **The warm-start relation** (Dabas, arXiv:2611.04094, §2.3, p.6: "The next search starts from
S⁻ and cannot increase its potential at the new penalty").
For an instance satisfying the standing assumptions, `λ ≥ 0`, `τ > 0`, a capacity-feasible start
`S₀` and every run of `Local(λ, τ; S₀)` ending at `S`, `Φ_λ(S) ≤ Φ_λ(S₀)`.

**Formalization Note.** Stated for every run and every capacity-feasible start; §2.3 applies it
with `S₀ = S⁻` and `λ = λ⁺`, which gives `b + λ⁺(n − q⁺) ≤ a + λ⁺(n − q⁻)`. -/
theorem warm_start_descent (I : Inst) (hI : I.Std) (lam τ : ℝ) (hlam : 0 ≤ lam) (hτ : 0 < τ)
    (S0 S : Sol I) (N : ℕ) (h0 : S0.CapFeasible) (hrun : LocalRun lam τ S0 S N) :
    Phi lam S ≤ Phi lam S0 := by sorry

end CFLOutliers
