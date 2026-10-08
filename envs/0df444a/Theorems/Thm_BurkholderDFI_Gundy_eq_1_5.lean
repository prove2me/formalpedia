-- Prove2me | Theorems.Thm_BurkholderDFI_Gundy_eq_1_5
-- name    : BurkholderDFI.Gundy.eq_1_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:24.280708+00:00
-- url     : https://prove2.me/theorems/5751bff5-0c24-4c23-9b98-deafb14b28b9
-- title:
--   (1.5) — the weak-type maximal inequality $\lambda^p P(f^*>\lambda)\le\|f\|_p^p$, $1\le p<\infty$
-- statement:
--   Let $f=(f_1,f_2,\dots)$ be a martingale, or a nonnegative submartingale, relative to $\mathcal A_1,\mathcal A_2,\dots$ on a probability space $(\Omega,\mathcal A,P)$, let $f^*=\sup_{n\ge1}|f_n|$ be its maximal function and $\|f\|_p=\sup_{n\ge1}(E|f_n|^p)^{1/p}$. For every $1\le p<\infty$ and every $\lambda>0$,
--   $$\lambda^p\,P(f^*>\lambda)\le\|f\|_p^p.$$
--
--   This is the weak-type form of Doob's maximal inequality, obtained in the paper by applying Doob's inequality (1.1) to the submartingale $|f_n|^p$. With $p=1$ it bounds the probability that the martingale ever leaves $[-\lambda,\lambda]$ by $\|f\|_1/\lambda$.
--
--   **Formalization Note** Both sides are computed in $[0,\infty]$; when $f$ is not $L^p$-bounded the right side is $\infty$ and the inequality is trivially true, as in the paper. The conventions on Mathlib's index $0$ and on "nonnegative" (almost surely) are those of the shared definitions: the index-$0$ value is never read, and every process of the paper extends to one of Mathlib's by $f_0:=E(f_1\mid\mathcal A_0)$.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), (1.5), p. 20

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.Gundy

/-- (1.5), p. 20: `λ^p P(f^* > λ) ≤ ‖f‖_p^p` for `1 ≤ p < ∞`, `f` a martingale or a nonnegative
submartingale. -/
theorem eq_1_5 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (p : ℝ) (hp : 1 ≤ p) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < BurkholderDFI.SquareFnLp.maxFn f ω} ≤ BurkholderDFI.SquareFnLp.pNorm P p f ^ p := by sorry

end BurkholderDFI.Gundy
