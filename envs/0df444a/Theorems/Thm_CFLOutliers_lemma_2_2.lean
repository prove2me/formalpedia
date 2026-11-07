-- Prove2me | Theorems.Thm_CFLOutliers_lemma_2_2
-- name    : CFLOutliers.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:38:46.624194+00:00
-- url     : https://prove2.me/theorems/a0993c4d-6ec3-4cfa-81ce-ec0d5c70fb90
-- title:
--   Lemma 2.2 — merging two penalty solutions that bracket the quota, in polynomial time
-- statement:
--   Let $S^-$, $S^+$ be capacity-feasible solutions with $q^-=|C_{S^-}|<q\le q^+=|C_{S^+}|$, let $a=c(S^-)$, $b=c(S^+)$, $\theta=(q-q^-)/(q^+-q^-)$, and let $M\ge 0$ bound the opening cost of every facility open in $S^+$ and closed in $S^-$. Costs are nonnegative; no metric is assumed.
--
--   1. **Bound.** There is a capacity-feasible solution serving at least $q$ clients and costing at most
--   $$\min\{b,\ a+\theta b+M\}.\tag{3}$$
--   2. **Polynomial time.** There are one Turing machine and one constant $c$ such that, for every rational instance and all such $S^-$, $S^+$ and rational $M$, the machine computes such a solution from the encoded input $(\text{instance},S^-,S^+,M)$ within $c\,(N+2)^c$ steps, where $N$ is the input length.
--
--   Combined with Theorem 2.1 this is the quota-recovery step: it turns two penalty solutions on either side of the quota into one feasible solution, paying at most one extra opening cost $M$.
--
--   Differences from the source:
--   - generalization: "The lemma requires nonnegative costs" → nonnegative service costs c_ij and opening costs f_i; the facility–facility and client–client entries of c are unconstrained; reason: only c_ij and f_i enter the cost c(S), and Appendix A uses no other distance
--   - reading: "In polynomial time, one can construct" → one Mathlib TM2 machine and one constant c, chosen before the input, outputting the encoded solution within c·(N + 2)^c steps on the encoded (instance, S⁻, S⁺, M) with rational data; reason: the paper names no machine model; a polynomial-time algorithm in any standard model is simulated by a Turing machine with polynomial overhead, and a machine reads rational data
--   - generalization: S⁻ and S⁺ the consecutive penalty-search solutions of §2.1 (p.4) → any two capacity-feasible solutions with |C_{S⁻}| < q ≤ |C_{S⁺}| on any instance with nonnegative service and opening costs; reason: Appendix A uses only capacity feasibility, the two served counts and nonnegative costs; the penalty solutions are a special case
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), Lemma 2.2, p.5, display (3); proof Appendix A, pp.12–14

import Mathlib
import Definitions.Def_CFLOutliers_MergeSpec
import Definitions.Def_CFLOutliers_encInst
import Definitions.Def_CFLOutliers_OutputsWithin

namespace CFLOutliers

open OnlineCRS.Combine (Sym)

/-- **Lemma 2.2** (Dabas, arXiv:2611.04094, p.5; proof Appendix A, pp.12–14).
Let `S⁻`, `S⁺` be capacity-feasible with `q⁻ = |C_{S⁻}| < q ≤ q⁺ = |C_{S⁺}|`, `a = c(S⁻)`,
`b = c(S⁺)`, `θ = (q − q⁻)/(q⁺ − q⁻)`, and let `M ≥ 0` bound the opening cost of every facility
open in `S⁺` and closed in `S⁻`. Costs are nonnegative; no metric is assumed.
1. (**Bound**) there is a capacity-feasible solution serving at least `q` clients of cost at most
   `min{b, a + θ b + M}` (3);
2. (**Polynomial time**) one Turing machine computes such a solution from the encoded input
   `(instance, S⁻, S⁺, M)` (rational data) within `c (N + 2)^c` steps, `N` the input length.

**Formalization Note.** Clause 1 is over real data, clause 2 over rational inputs `RInst`
(lengths as stated by `Shaped`; no triangle inequality). "Nonnegative costs" are the service
costs `c_{ij}` and the opening costs `f_i`; the other entries of `c` do not enter any cost. -/
theorem lemma_2_2 :
    (∀ (I : Inst), (∀ i j, 0 ≤ I.cFC i j) → (∀ i, 0 ≤ I.f i) →
      ∀ (Sm Sp : Sol I), Sm.CapFeasible → Sp.CapFeasible →
      (served Sm).card < I.q → I.q ≤ (served Sp).card →
      ∀ M : ℝ, 0 ≤ M → (∀ i ∈ Sp.openSet, i ∉ Sm.openSet → I.f i ≤ M) →
      ∃ S : Sol I, MergeSpec Sm Sp M S) ∧
    (∃ (Mach : Turing.TM2ComputableAux Sym Sym) (c : ℕ),
      ∀ (I : RInst), I.Shaped → (∀ i j, 0 ≤ I.toInst.cFC i j) → (∀ i, 0 ≤ I.toInst.f i) →
      ∀ (Sm Sp : Sol I.toInst), Sm.CapFeasible → Sp.CapFeasible →
      (served Sm).card < I.toInst.q → I.toInst.q ≤ (served Sp).card →
      ∀ M : ℚ, 0 ≤ M → (∀ i ∈ Sp.openSet, i ∉ Sm.openSet → I.toInst.f i ≤ (M : ℝ)) →
      ∃ S : Sol I.toInst, MergeSpec Sm Sp (M : ℝ) S ∧
        OutputsWithin Mach (encMergeIn I Sm Sp M) (encSol S)
          (c * ((encMergeIn I Sm Sp M).length + 2) ^ c)) := by sorry

end CFLOutliers
