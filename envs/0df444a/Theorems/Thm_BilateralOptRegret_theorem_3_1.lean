-- Prove2me | Theorems.Thm_BilateralOptRegret_theorem_3_1
-- name    : BilateralOptRegret.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:34.076499+00:00
-- url     : https://prove2.me/theorems/21f49c2c-96b1-4846-8c34-8ef1e2d25b22
-- title:
--   Theorem 3.1 — phased successive elimination has regret $O(T^{2/3}\log^{9/2}T)$
-- statement:
--   There are absolute constants $c_0\ge1$ and $C>0$ with the following property. For every horizon $T\ge2$, every law $L$ on $[0,1]^2$ of the transformed valuations, and every i.i.d. sequence of draws from $L$, Algorithm 1 with Refine given by Algorithm 3 and $A(K,\delta)=c_0\ell_K^6\log(24K^3/\delta)$, which observes only the trade bits, has expected regret
--   $$R_T=T\sup_{x\in[0,1]^2}r(x)-\mathbb E\Big[\sum_{t=1}^Tr(x_t)\Big]\le C\,T^{2/3}\log^{9/2}T.$$
--   This settles the regret rate of profit maximization in repeated bilateral trade under one-bit feedback up to logarithmic factors: two prices cost no more than one. The law $L$ is arbitrary: the two valuations may be correlated, and may have atoms.
--
--   Differences from the source:
--   - generalization: "there exists an algorithm" → the explicit Algorithm 1 with Algorithm 3, for every way of making its choices; reason: it witnesses the existential; the bare form would also follow from an adversarial bound for a different algorithm, and the paper's contribution is this algorithm
--   - encoding: $O(\cdot)$ → $\exists C>0$ for all $T\ge2$ and all laws, with $c_0$ and $C$ before $T$; reason: Algorithm 1 requires $T\ge2$ and at $T=1$ the right side is $0$; "for arbitrary joint distributions" (p.5) makes $C$ uniform in $L$; $c_0$ is inside the algorithm
--   - encoding: an algorithm → a deterministic, horizon-dependent policy on the trade bits; reason: Algorithm 1 takes $T$ as input and uses no internal randomness, so the internal randomization in (3) is empty
--   - encoding: $(S_t,B_t)$, prices $(p_t,q_t)$, rounds $1,\dots,T$ → $X_t=(S_t,1-B_t)$, $x_t=(p_t,1-q_t)$ as on p.13; rounds $0,\dots,T-1$; natural log; $\Omega:$ `Type`; reason: same instances; the sanity file checks the bridge to prices
--   - encoding: "choose" (an arbitrary choice) → every selection rule `IsSel` on finite sets; reason: the statement holds for each way of resolving the choice by a function of the candidate set; no choice reads the law
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Theorem 3.1, p.14 (proof §9, p.42)

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Regret
import Definitions.Def_BilateralOptRegret_Phased
import Definitions.Def_BilateralOptRegret_Refine

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Theorem 3.1**, Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.14; proof §9, p.42: the regret of phased successive elimination.

There are absolute constants `c₀ ≥ 1` and `C > 0` such that for every horizon `T ≥ 2`, every law `L` on `[0,1]²` and every i.i.d. run, Algorithm 1 with Refine = Algorithm 3 and `A(K, δ) = c₀ ℓ_K⁶ log(24K³/δ)`, seeing only the trade bits, has
`R_T ≤ C T^{2/3} (log T)^{9/2}`, where `R_T` is measured against the best price pair in all of `[0,1]²`.

**Formalization Note.** The printed "there exists an algorithm" is witnessed by the paper's explicit algorithm, for every way of making its choices (`sel`, `pick`). The constants come before `T` since `c₀` is inside the algorithm. The policy's
signature makes the feedback one bit. `L` is any `IsValLaw`: joint, possibly correlated and with atoms. `log` is natural. -/
theorem theorem_3_1 :
    ∃ c₀ C : ℝ, 1 ≤ c₀ ∧ 0 < C ∧ ∀ T : ℕ, 2 ≤ T →
      ∀ (sel : Finset (Idx (nOf T)) → Idx (nOf T)) (pick : Finset (Act (nOf T)) → Act (nOf T)),
        IsSel sel → IsSel pick →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (L : Measure (ℝ × ℝ)) (X : ℕ → Ω → ℝ × ℝ),
          IsValLaw L → IsIIDRun P X L →
          regret P X L (phasedPolicy (paperA c₀) T (refineAlg sel) pick) T ≤
            C * (T : ℝ) ^ ((2 : ℝ) / 3) * Real.log (T : ℝ) ^ ((9 : ℝ) / 2) := by sorry

end BilateralOptRegret
