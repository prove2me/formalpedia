-- Prove2me | Theorems.Thm_BurkholderDFI_CondSquare_theorem_21_1
-- name    : BurkholderDFI.CondSquare.theorem_21_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:02.015251+00:00
-- url     : https://prove2.me/theorems/dbb89f36-ba0b-4806-b396-efadb8a5cfa4
-- title:
--   Theorem 21.1 — EΦ(f*) ≤ cEΦ(s(f)) + cEΦ(d*) for every martingale and every Φ of moderate growth
-- statement:
--   Let $\Phi:[0,\infty]\to[0,\infty]$ satisfy the conditions of Section 7: $\Phi$ is nondecreasing and continuous, $\Phi(0)=0$, and $\Phi(2\lambda)\le c_{(6.1)}\Phi(\lambda)$ for $\lambda>0$. Let $f=(f_1,f_2,\dots)$ be a martingale relative to $\mathcal A_1,\mathcal A_2,\dots$ with difference sequence $d$, maximal function $f^*=\sup_n|f_n|$, largest jump $d^*=\sup_k|d_k|$ and conditional square function
--   $$
--   s(f)=\Big[\sum_{k=1}^\infty E\big(d_k^2\mid\mathcal A_{k-1}\big)\Big]^{1/2}.
--   $$
--   Then there is a constant $c$, depending only on $c_{(6.1)}$, such that
--   $$
--   E\Phi(f^*)\le c\,E\Phi(s(f))+c\,E\Phi(d^*).
--   $$
--
--   No convexity of $\Phi$ is required, in contrast to the inequality $E\Phi(S(f))\le cE\Phi(s(f))$, which the paper notes cannot hold for general $\Phi$. In the case of independent mean-zero differences, $s(f)$ is deterministic and the theorem yields the upper half of Rosenthal's inequality.
--
--   **Formalization Note** The order of quantifiers expresses "the choice of $c$ depends only on $c_{(6.1)}$": for every growth constant there is one $C>0$ that works for every probability space (in Lean's universe `Type`), every filtration, every martingale and every admissible $\Phi$; one constant multiplies both terms, as printed. The martingale is a Mathlib martingale for a filtration indexed from $0$ (its $0$-th $\sigma$-field is $\mathcal A_0$, used in $E(d_1^2\mid\mathcal A_0)$); this is no restriction, since a martingale relative to $\mathcal A_1,\mathcal A_2,\dots$ extends by $f_0:=E(f_1\mid\mathcal A_0)$, and the statement reads only $f_n$, $n\ge1$ (with $d_1=f_1$). $f^*$, $d^*$, $s(f)$ and the expectations take values in $[0,\infty]$; the conditional expectations in $s(f)$ are extended conditional expectations, so no integrability of $d_k^2$ is assumed. The paper's exclusion of $\Phi\equiv0$ is dropped, since the inequality is trivial for it.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §21, Theorem 21.1, (21.1), p. 39

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.CondSquare

/-- Theorem 21.1, p. 39: for every `Φ` satisfying the conditions of Section 7 and every martingale
`f`, `EΦ(f^*) ≤ cEΦ(s(f)) + cEΦ(d^*)`, where `c` depends only on the growth constant `c_(6.1)`. -/
theorem theorem_21_1 (c : ℝ≥0) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ), Martingale f ℱ P →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, BurkholderDFI.SquareFnLp.IsPhi Φ c →
          ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.maxFn f ω) ∂P
            ≤ (C : ℝ≥0∞) * ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.condSqFn ℱ P f ω) ∂P
              + (C : ℝ≥0∞) * ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.maxFn (BurkholderDFI.SquareFnLp.dseq f) ω) ∂P := by sorry

end BurkholderDFI.CondSquare
