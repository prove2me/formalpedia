-- Prove2me | Theorems.Thm_DerivativeChainPhaseLock_actual_odd_orientation_or_balance
-- name    : DerivativeChainPhaseLock.actual_odd_orientation_or_balance
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T06:19:19.893827+00:00
-- url     : https://prove2.me/theorems/b25a9cbc-51a8-4cb4-bb60-e520ccfe0724
-- title:
--   Actual odd-moment orientation with the zero-center alternative
-- statement:
--   For each natural number $k$, write $I_k=\{0,\ldots,k-1\}$, with $I_0=\varnothing$. Let $p\in \mathbb C[X]$, $m\in \mathbb N$, $q\in \mathbb N$, $A\in \operatorname{Multiset}\!\left(\mathbb C\right)$, $B\in \operatorname{Multiset}\!\left(\mathbb C\right)$, $Z\in \operatorname{Multiset}\!\left(\mathbb C\right)$, $a\in \mathbb C$, $ε\in \mathbb R$, $ρ\in \mathbb R$. Assume
--
--   $$
--   \begin{aligned}
--   &\operatorname{Monic}\!\left(p\right)\\
--   &\operatorname{Odd}\!\left(q\right)\\
--   &\left(q \le m\right)\\
--   &\left(m \le \operatorname{natDegree}\!\left(p\right)\right)\\
--   &\forall j\in \mathbb N,\quad \bigl(\left(j < q\right)\Longrightarrow \bigl(\operatorname{Odd}\!\left(j\right)\Longrightarrow \left(\operatorname{appellCoefficients}\!\left(p, j\right) = 0\right)\bigr)\bigr)\\
--   &\left(\operatorname{roots}\!\left(\operatorname{iterate}\!\left(\operatorname{coe}\!\left(\mathrm D\right), \left(\operatorname{natDegree}\!\left(p\right) - m\right), p\right)\right) = \left(\left(A + B\right) + Z\right)\right)\\
--   &\left(0 \le ε\right)\\
--   &\left(0 \le ρ\right)\\
--   &\forall z\in \mathbb C,\quad \bigl(\left(z\in A\right)\Longrightarrow \left(\left\|\left(z - a\right)\right\| \le \left(ε \, \left\|a\right\|\right)\right)\bigr)\\
--   &\forall z_{1}\in \mathbb C,\quad \bigl(\left(z_{1}\in B\right)\Longrightarrow \left(\left\|\left(z_{1} + a\right)\right\| \le \left(ε \, \left\|a\right\|\right)\right)\bigr)\\
--   &\forall z_{2}\in \mathbb C,\quad \bigl(\left(z_{2}\in Z\right)\Longrightarrow \left(\left\|z_{2}\right\| \le \left(ρ \, \left\|a\right\|\right)\right)\bigr)
--   \end{aligned}
--   $$
--
--   Then
--
--   $$
--   \left(\left(\operatorname{multisetPowerSum}\!\left(\operatorname{roots}\!\left(\operatorname{iterate}\!\left(\operatorname{coe}\!\left(\mathrm D\right), \left(\operatorname{natDegree}\!\left(p\right) - m\right), p\right)\right), q\right) = \left(\left(\left(-q\right) \, \operatorname{choose}\!\left(m, q\right)\right) \, \operatorname{appellCoefficients}\!\left(p, q\right)\right)\right) \land \left(\bigl(\left(a = 0\right)\Longrightarrow \left(\operatorname{appellCoefficients}\!\left(p, q\right) = 0\right)\bigr) \land \left(\bigl(\left(\operatorname{appellCoefficients}\!\left(p, q\right) = 0\right)\Longrightarrow \left(\left(a = 0\right) \lor \left(\left|\operatorname{clusterImbalance}\!\left(A, B\right)\right| \le \operatorname{clusterErrorBudget}\!\left(A, B, Z, q, ε, ρ\right)\right)\right)\bigr) \land \bigl(\left(a \ne 0\right)\Longrightarrow \bigl(\left(\operatorname{clusterErrorBudget}\!\left(A, B, Z, q, ε, ρ\right) < \left|\operatorname{clusterImbalance}\!\left(A, B\right)\right|\right)\Longrightarrow \left(\left(0 < \operatorname{Re}\left(\left(\operatorname{multisetPowerSum}\!\left(\operatorname{roots}\!\left(\operatorname{iterate}\!\left(\operatorname{coe}\!\left(\mathrm D\right), \left(\operatorname{natDegree}\!\left(p\right) - m\right), p\right)\right), q\right) \, \operatorname{star}\!\left(\left(\operatorname{clusterImbalance}\!\left(A, B\right) \, \left(a\right)^{q}\right)\right)\right)\right)\right) \land \left(\left|\operatorname{arg}\!\left(\frac{\operatorname{multisetPowerSum}\!\left(\operatorname{roots}\!\left(\operatorname{iterate}\!\left(\operatorname{coe}\!\left(\mathrm D\right), \left(\operatorname{natDegree}\!\left(p\right) - m\right), p\right)\right), q\right)}{\left(\operatorname{clusterImbalance}\!\left(A, B\right) \, \left(a\right)^{q}\right)}\right)\right| \le \operatorname{arcsin}\!\left(\frac{\operatorname{clusterErrorBudget}\!\left(A, B, Z, q, ε, ρ\right)}{\left|\operatorname{clusterImbalance}\!\left(A, B\right)\right|}\right)\right)\right)\bigr)\bigr)\right)\right)\right)
--   $$
--
--   The named functions `DerivativeChainContinuation.appellCoefficients`, `DerivativeChainPhaseLock.clusterErrorBudget`, `DerivativeChainPhaseLock.clusterImbalance`, `DerivativeChainPhaseLock.multisetPowerSum` retain their exact imported definitions. Relate the actual odd moment to the signed cluster counts and control its error. The conclusion retains the zero-center alternative instead of inferring balance there.
--
--   Formalization Note. Natural-number subtraction is truncated. Named functions, index embeddings and field projections use their exact imported definitions.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/OddMomentOrientation.lean, lines 53-95, SHA-256 2f0ba12fa5cc223342070846846b7de9e5594f8676a33d43225cb596bc301cb7. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_MomentErrorBounds
import Definitions.Def_DerivativeChainAnalytic_OddMomentPersistence
import Definitions.Def_DerivativeChainContinuation_AppellCoefficients
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainFiniteHistory
end DerivativeChainFiniteHistory
namespace DerivativeChainPhaseLock
end DerivativeChainPhaseLock
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Polynomial DerivativeChainContinuation
open DerivativeChainPhaseLock

theorem DerivativeChainPhaseLock.actual_odd_orientation_or_balance (p : Polynomial ℂ) (hp : p.Monic)
    (m q : ℕ) (hq : Odd q) (hqm : q ≤ m) (hm : m ≤ p.natDegree)
    (hzero : ∀ j<q, Odd j → appellCoefficients p j=0)
    (A B Z : Multiset ℂ)
    (hpartition : ((derivative^[p.natDegree-m]) p).roots=A+B+Z)
    (a : ℂ) (ε ρ : ℝ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (hA : ∀ z∈A, ‖z-a‖ ≤ ε*‖a‖)
    (hB : ∀ z∈B, ‖z+a‖ ≤ ε*‖a‖)
    (hZ : ∀ z∈Z, ‖z‖ ≤ ρ*‖a‖) :
    let S := multisetPowerSum ((derivative^[p.natDegree-m]) p).roots q;
    let δ := clusterImbalance A B;
    let E := clusterErrorBudget A B Z q ε ρ;
    S=-(q:ℂ)*(m.choose q:ℂ)*appellCoefficients p q ∧
      (a=0 → appellCoefficients p q=0) ∧
      (appellCoefficients p q=0 → a=0 ∨ |δ| ≤ E) ∧
      (a ≠ 0 → E < |δ| → 0 < (S*star ((δ:ℂ)*a^q)).re ∧
        |(S/((δ:ℂ)*a^q)).arg| ≤ Real.arcsin (E/|δ|)) := by sorry
