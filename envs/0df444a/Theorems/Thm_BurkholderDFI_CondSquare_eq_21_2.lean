-- Prove2me | Theorems.Thm_BurkholderDFI_CondSquare_eq_21_2
-- name    : BurkholderDFI.CondSquare.eq_21_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:42.578355+00:00
-- url     : https://prove2.me/theorems/fbf86cb1-4e69-44a9-8f51-4a26e342c819
-- title:
--   (21.2) — good-λ inequality P(f* > βλ, s(f) ∨ d* ≤ δλ) ≤ δ²/(β − δ − 1)² · P(f* > λ)
-- statement:
--   Let $f=(f_1,f_2,\dots)$ be a martingale relative to $\mathcal A_1,\mathcal A_2,\dots$, with difference sequence $d$, maximal function $f^*=\sup_n|f_n|$, largest jump $d^*=\sup_k|d_k|$, and conditional square function $s(f)=\big[\sum_{k\ge1}E(d_k^2\mid\mathcal A_{k-1})\big]^{1/2}$. Let $\beta>1$ and $0<\delta<\beta-1$. Then for every $\lambda>0$,
--   $$
--   P\big(f^*>\beta\lambda,\ s(f)\vee d^*\le\delta\lambda\big)\le\frac{\delta^2}{(\beta-\delta-1)^2}\,P(f^*>\lambda).
--   $$
--
--   This is the distribution function (good-$\lambda$) inequality from which Theorem 21.1 follows by Lemma 7.1: the right-hand factor tends to $0$ as $\delta\to0$ for fixed $\beta$.
--
--   **Formalization Note** The martingale is a Mathlib martingale for a filtration indexed from $0$ (its $0$-th $\sigma$-field is $\mathcal A_0$), which is no restriction (extend by $f_0:=E(f_1\mid\mathcal A_0)$); the statement reads only $f_n$, $n\ge1$, with $d_1=f_1$. The conditional expectations in $s(f)$ are extended ($[0,\infty]$-valued) conditional expectations, so no integrability of $d_k^2$ is assumed. $f^*$, $d^*$, $s(f)$ take values in $[0,\infty]$ and $s(f)\vee d^*$ is their maximum.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §21, (21.2), p. 39

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.CondSquare

/-- (21.2), p. 39: for a martingale `f`, `β > 1` and `0 < δ < β − 1`,
`P(f^* > βλ, s(f) ∨ d^* ≤ δλ) ≤ δ²/(β − δ − 1)² · P(f^* > λ)` for every `λ > 0`. -/
theorem eq_21_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P)
    (β δ : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hδβ : δ < β - 1) (l : ℝ) (hl : 0 < l) :
    P {ω | ENNReal.ofReal (β * l) < BurkholderDFI.SquareFnLp.maxFn f ω ∧
          max (BurkholderDFI.SquareFnLp.condSqFn ℱ P f ω) (BurkholderDFI.SquareFnLp.maxFn (BurkholderDFI.SquareFnLp.dseq f) ω) ≤ ENNReal.ofReal (δ * l)}
      ≤ ENNReal.ofReal (δ ^ 2 / (β - δ - 1) ^ 2) * P {ω | ENNReal.ofReal l < BurkholderDFI.SquareFnLp.maxFn f ω} := by sorry

end BurkholderDFI.CondSquare
