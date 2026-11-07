-- Prove2me | Theorems.Thm_CFLOutliers_theorem_2_1
-- name    : CFLOutliers.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:04.055668+00:00
-- url     : https://prove2.me/theorems/afaa82f4-3d40-4f20-80be-8215929ac35a
-- title:
--   Theorem 2.1 — the signed penalty comparison $c(S)+3\lambda(q-|C_S|)\le 5\,\mathrm{OPT}+6m\tau$
-- statement:
--   Fix an instance satisfying the standing assumptions, with quota $q>0$ and a capacity-feasible solution serving at least $q$ clients. For every penalty $\lambda\ge 0$, every improvement threshold $\tau>0$ and every terminal solution $S$ of the penalty local search,
--
--   $$c(S)+3\lambda\bigl(q-|C_S|\bigr)\le 5\,\mathrm{OPT}+6m\tau.\tag{2}$$
--
--   Here $q-|C_S|$ is a signed quantity: it is negative when $S$ serves more than $q$ clients. Because the same coefficient multiplies $q$ and $|C_S|$, the penalty term cancels when two penalty solutions are averaged to served count $q$; this is the comparison that ordinary penalty approximation guarantees do not provide.
--
--   **Formalization Note** "Terminal" is the termination condition of §3.2: an optimal penalty assignment, and every exact add change, open certificate (9) and close certificate (10) at least $-\tau$.
--
--   Differences from the source:
--   - generalization: a finite metric space with distances c → a pseudometric on the index set F ⊔ C (distinct points may be at distance 0); reason: it covers every metric instance, including a facility co-located with a client; no step of the paper uses positivity of distances
--   - generalization: "every terminal solution S of the penalty local search" (an output of Local) → every solution satisfying the termination condition IsTerminal of §3.2; reason: every output of Local satisfies it, and the proof of §4 uses only the termination condition
--   - encoding: O an optimal solution serving exactly q clients, of cost OPT → OPT the minimum over capacity-feasible solutions with |C_S| ≥ q, with the instance assumed feasible; reason: p.2: nonnegative costs allow an optimum serving exactly q clients, so the two minima are the same number
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), Theorem 2.1, p.4 (restated p.9), display (2); proof §4, pp.9–12

import Mathlib
import Definitions.Def_CFLOutliers_LocalRun
import Definitions.Def_CFLOutliers_OPT

namespace CFLOutliers

/-- **Theorem 2.1** (Dabas, arXiv:2611.04094, p.4, restated p.9; proof §4, pp.9–12).
Fix an instance satisfying the standing assumptions with quota `q > 0` that has a feasible
solution. For every penalty `λ ≥ 0`, every improvement threshold `τ > 0` and every terminal
solution `S` of `Local(λ, τ; ·)`,
`c(S) + 3λ(q − |C_S|) ≤ 5 OPT + 6 m τ`  (2).

**Formalization Note.** `q − |C_S|` is a signed real number (it is negative when `S` serves more
than `q` clients). `IsTerminal` is the termination condition of §3.2 (optimal penalty
assignment, every exact add change, open and close certificate at least `−τ`); every output of
`Local` satisfies it. -/
theorem theorem_2_1 (I : Inst) (hI : I.Std) (hq : 0 < I.q) (hF : I.Feasible)
    (lam τ : ℝ) (hlam : 0 ≤ lam) (hτ : 0 < τ) (S : Sol I) (hS : IsTerminal lam τ S) :
    cost S + 3 * lam * ((I.q : ℝ) - ((served S).card : ℝ)) ≤
      5 * OPT I + 6 * (I.m : ℝ) * τ := by sorry

end CFLOutliers
