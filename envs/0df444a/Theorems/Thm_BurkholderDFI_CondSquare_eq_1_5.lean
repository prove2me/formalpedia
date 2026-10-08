-- Prove2me | Theorems.Thm_BurkholderDFI_CondSquare_eq_1_5
-- name    : BurkholderDFI.CondSquare.eq_1_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:23.737654+00:00
-- url     : https://prove2.me/theorems/241a353d-b9b8-4cc2-9dbc-90a44bf4378c
-- title:
--   (1.5) — Doob's weak-type inequality λ^p P(f* > λ) ≤ ‖f‖_p^p, 1 ≤ p < ∞
-- statement:
--   Let $f=(f_1,f_2,\dots)$ be a martingale, or a nonnegative submartingale, relative to $\mathcal A_1,\mathcal A_2,\dots$, and let $f^*=\sup_{n\ge1}|f_n|$ and $\|f\|_p=\sup_{n\ge1}(E|f_n|^p)^{1/p}$. Then for every $1\le p<\infty$ and every $\lambda>0$,
--   $$
--   \lambda^p\,P(f^*>\lambda)\le\|f\|_p^p .
--   $$
--
--   This is Doob's maximal inequality in weak-type form, obtained in the paper by applying (1.1) to the submartingale $(|f_n|^p)_{n\ge1}$. It is used with $p=2$ in the proof of (21.2).
--
--   **Formalization Note** The filtration is indexed from $0$ (its $0$-th $\sigma$-field is $\mathcal A_0$) and the martingale property is Mathlib's, which also constrains the index-$0$ term; this is no restriction, since any martingale (submartingale) relative to $\mathcal A_1,\mathcal A_2,\dots$ extends to index $0$ by $f_0:=E(f_1\mid\mathcal A_0)$, and the statement reads only $f_n$, $n\ge1$. "Nonnegative" means $f_n\ge0$ almost surely for every $n\ge1$. Both sides are in $[0,\infty]$; when $\|f\|_p=\infty$ the inequality is trivial.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §1, (1.5), p. 20 (fact from Doob [15])

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.CondSquare

/-- (1.5), p. 20: `λ^p P(f^* > λ) ≤ ‖f‖_p^p` for `1 ≤ p < ∞`, `f` a martingale or a nonnegative
submartingale. -/
theorem eq_1_5 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (p : ℝ) (hp : 1 ≤ p) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < BurkholderDFI.SquareFnLp.maxFn f ω} ≤ BurkholderDFI.SquareFnLp.pNorm P p f ^ p := by sorry

end BurkholderDFI.CondSquare
