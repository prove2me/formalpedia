-- Prove2me | Theorems.Thm_AllocationIndices_vigour_bandit_indexable
-- name    : AllocationIndices.vigour_bandit_indexable
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-24T02:59:51.548206+00:00
-- url     : https://prove2.me/theorems/94ef01d6-b22d-4cd8-9b59-4d0212d0084c
-- title:
--   Theorem 6.5: if ψ is strictly increasing the vigour bandit is indexable, and if W**(x) is strictly increasing its Whittle index is W**(x)
-- statement:
--   **Theorem 6.5** (p. 159). (i) If $\psi$ is increasing, the bandit is indexable. (ii) If additionally $W^{**}(x) = \big(r(x)[1 - \psi(x)] - r(x+1)[1 - \psi(x+1)]\big)/\big(\psi(x+1) - \psi(x)\big)$ is increasing over $1 \le x \le k$, then the bandit has Whittle index $W(x) = W^{**}(x)$, $1 \le x \le k$.
--
--   Formally, for the vigour bandit (active: down at rate $\nu(x)$ earning $r(x)$; passive: up at rate $\rho(x)$ earning nothing; rates in $[0, 1]$, $\nu(1) = \rho(k) = 0$; $r$ increasing and nonnegative): if $\psi(y) = \nu(y)/(\nu(y) + \rho(y-1))$ is strictly increasing over the thresholds $0 \le y \le k$ (with $\psi(0) = 0$, $\psi(k) = 1$), the bandit is indexable; and if moreover $W^{**}$ is strictly increasing over the states, $W(x) = W^{**}(x)$ for every state $x$. "Increasing" is read as strictly increasing, as in Theorem 6.4.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §6.5 pp. 158-159, Theorem 6.5 (the bandit of Example 6.1; proof 'similar to the above', i.e. to Theorem 6.4)

import Definitions.Def_AllocationIndices_Restless

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

namespace AllocationIndices

/-- **Theorem 6.5** (p. 159). For the vigour bandit (active: down at rate `ν(x)` earning `r(x)`;
passive: up at rate `ρ(x)` earning nothing; `ν(1) = ρ(k) = 0`; `r` increasing and nonnegative):
(i) if `ψ(y) = ν(y)/(ν(y) + ρ(y−1))` is (strictly) increasing over the thresholds, the bandit is
indexable; (ii) if additionally `W**(x) = (r(x)(1−ψ(x)) − r(x+1)(1−ψ(x+1)))/(ψ(x+1) − ψ(x))` is
(strictly) increasing over the states, the bandit has Whittle index `W(x) = W**(x)`. -/
theorem vigour_bandit_indexable {k : ℕ} (nu rho r : Fin k → ℝ)
    (hnu : ∀ x, nu x ∈ Set.Icc (0 : ℝ) 1) (hrho : ∀ x, rho x ∈ Set.Icc (0 : ℝ) 1)
    (hnu_bot : ∀ x : Fin k, x.val = 0 → nu x = 0)
    (hrho_top : ∀ x : Fin k, x.val + 1 = k → rho x = 0)
    (hr : Monotone r) (hr0 : ∀ x, 0 ≤ r x)
    (hpsi : StrictMonoOn (vigourShare nu rho) (Set.Iic k)) :
    Indexable (vigourBandit nu rho r hnu hrho) ∧
    (StrictMono (vigourIndex nu rho r) →
      ∀ x, whittleIndex (vigourBandit nu rho r hnu hrho) x = vigourIndex nu rho r x) := by sorry

end AllocationIndices
