-- Prove2me | Theorems.Thm_AllocationIndices_spinning_plates_indexable
-- name    : AllocationIndices.spinning_plates_indexable
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:00:33.755128+00:00
-- url     : https://prove2.me/theorems/4259739d-7e1d-47aa-9fcd-bf0439848f19
-- title:
--   Theorem 6.4: if ϕ is strictly decreasing the spinning plates asset is indexable, and if W*(x) is strictly decreasing its Whittle index is W*(x)
-- statement:
--   **Theorem 6.4** (p. 157). (i) If $\phi$ is strictly decreasing over $1 \le x \le k+1$, the asset is indexable. (ii) If additionally $W^*(x) = \big(R(x+1) - R(x)\big)/\big(\phi(x) - \phi(x+1)\big)$ (6.11) is strictly decreasing over $1 \le x \le k$, then the asset has Whittle index $W(x) = W^*(x)$, $1 \le x \le k$.
--
--   Formally, for the spinning plates asset on $k$ states (rates in $[0, 1]$ with $\lambda(k) = \mu(1) = 0$, reward $r$ increasing and nonnegative): if $\phi(y) = \lambda(y-1)/(\lambda(y-1) + \mu(y))$ is strictly decreasing over the thresholds $0 \le y \le k$ (with $\phi(0) = 1$, $\phi(k) = 0$), then $W \le W'$ implies $E_0(W) \subseteq E_0(W')$, where $E_0(W)$ is the set of states in which some policy that is average-optimal from every initial state under subsidy $W$ takes the passive action; and if moreover $W^*$ is strictly decreasing over the states, $\inf\{W : x \in E_0(W)\} = W^*(x)$ for every state $x$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §6.5 pp. 156-158, Theorem 6.4 with its proof (the upper envelope (6.10) and its hinge points)

import Definitions.Def_AllocationIndices_Restless

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

namespace AllocationIndices

/-- **Theorem 6.4** (p. 157). For the spinning plates asset (rates `λ, μ` uniformized to
`[0, 1]` with `λ(k) = μ(1) = 0`, reward `r` increasing and nonnegative):
(i) if `ϕ(y) = λ(y−1)/(λ(y−1) + μ(y))` is strictly decreasing over the thresholds
`1 ≤ y ≤ k + 1` (here `0 ≤ y ≤ k`), the asset is indexable;
(ii) if additionally `W*(x) = (R(x+1) − R(x))/(ϕ(x) − ϕ(x+1))` is strictly decreasing over the
states, the asset has Whittle index `W(x) = W*(x)`. -/
theorem spinning_plates_indexable {k : ℕ} (lam mu r : Fin k → ℝ)
    (hlam : ∀ x, lam x ∈ Set.Icc (0 : ℝ) 1) (hmu : ∀ x, mu x ∈ Set.Icc (0 : ℝ) 1)
    (hlam_top : ∀ x : Fin k, x.val + 1 = k → lam x = 0)
    (hmu_bot : ∀ x : Fin k, x.val = 0 → mu x = 0)
    (hr : Monotone r) (hr0 : ∀ x, 0 ≤ r x)
    (hphi : StrictAntiOn (plateShare lam mu) (Set.Iic k)) :
    Indexable (spinningPlates lam mu r hlam hmu) ∧
    (StrictAnti (plateIndex lam mu r) →
      ∀ x, whittleIndex (spinningPlates lam mu r hlam hmu) x = plateIndex lam mu r x) := by sorry

end AllocationIndices
