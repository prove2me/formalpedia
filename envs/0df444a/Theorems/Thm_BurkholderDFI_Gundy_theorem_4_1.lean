-- Prove2me | Theorems.Thm_BurkholderDFI_Gundy_theorem_4_1
-- name    : BurkholderDFI.Gundy.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:53.316543+00:00
-- url     : https://prove2.me/theorems/777e0a9c-2124-4b78-8c67-fdabb57b57be
-- title:
--   Theorem 4.1 — Gundy's decomposition f = X + Y + Z of an L¹-bounded martingale, with one stopping time
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space, $\mathcal A_0\subseteq\mathcal A_1\subseteq\cdots$ a filtration, and $f=(f_1,f_2,\dots)$ an $L^1$-bounded martingale relative to $\mathcal A_1,\mathcal A_2,\dots$, i.e. $\|f\|_1=\sup_{n\ge1}E|f_n|<\infty$. Let $\lambda$ be a positive real number. Then there are martingales $X,Y,Z$, all relative to the same $\sigma$-fields $\mathcal A_1,\mathcal A_2,\dots$, with difference sequences $x,y,z$ ($y_1=Y_1$, $y_k=Y_k-Y_{k-1}$, and so on), such that
--
--   1. $f=X+Y+Z$, that is, $f_n=X_n+Y_n+Z_n$ for every $n\ge1$;
--   2. $$\|X\|_2^2\le 2\lambda\|f\|_1,$$ where $\|X\|_2=\sup_{n\ge1}(EX_n^2)^{1/2}$;
--   3. $$\Big\|\sum_{k=1}^\infty|y_k|\Big\|_1\le 4\|f\|_1;$$
--   4. $$P(Z^*>0)\le\|f\|_1/\lambda,$$ where $Z^*=\sup_{n\ge1}|Z_n|$.
--
--   The decomposition splits an $L^1$-bounded martingale at height $\lambda$ into an $L^2$-bounded part, a part of bounded total variation in $L^1$, and a part that vanishes identically outside an event of probability at most $\|f\|_1/\lambda$. It is the martingale analogue of the Calderón–Zygmund decomposition and reduces weak-type $(1,1)$ estimates for martingale operators to $L^2$ estimates.
--
--   **Formalization Note** The three martingales are Mathlib martingales for the same filtration as $f$; asserting this is no weaker than the paper, since a martingale indexed from $1$ extends to one indexed from $0$ by $X_0:=E(X_1\mid\mathcal A_0)$, and the decomposition (1) is required only for $n\ge1$, the paper's indices (Lean's index $0$ is otherwise free). Likewise the hypothesis that $f$ is a Mathlib martingale is no restriction. All norms are computed in $[0,\infty]$ with the lower Lebesgue integral: $\|X\|_2^2$ is the square of the supremum over $n\ge1$ of $\|X_n\|_2$ (not the norm of a limit), the left side of (3) is the integral of the series $\sum_{k\ge1}|y_k|$ with $y_1=Y_1$, and $\|f\|_1/\lambda$ is a quotient in $[0,\infty]$, finite since $\|f\|_1<\infty$ and $\lambda>0$.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), Theorem 4.1, (4.1)–(4.4), p. 23

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.Gundy

/-- Theorem 4.1, p. 23 (Gundy's decomposition, with one stopping time): an `L¹`-bounded martingale
`f` and `λ > 0` admit martingales `X, Y, Z` for the same filtration with `f = X + Y + Z`,
`‖X‖₂² ≤ 2λ‖f‖₁`, `‖Σ_{k ≥ 1} |y_k|‖₁ ≤ 4‖f‖₁` and `P(Z^* > 0) ≤ ‖f‖₁/λ`. -/
theorem theorem_4_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P) (hL1 : BurkholderDFI.SquareFnLp.pNorm P 1 f < ⊤)
    (l : ℝ) (hl : 0 < l) :
    ∃ X Y Z : ℕ → Ω → ℝ, Martingale X ℱ P ∧ Martingale Y ℱ P ∧ Martingale Z ℱ P ∧
      (∀ n, 1 ≤ n → f n = X n + Y n + Z n) ∧
      BurkholderDFI.SquareFnLp.pNorm P 2 X ^ (2 : ℝ) ≤ ENNReal.ofReal (2 * l) * BurkholderDFI.SquareFnLp.pNorm P 1 f ∧
      ∫⁻ ω, ∑' k : ℕ, ENNReal.ofReal |BurkholderDFI.SquareFnLp.dseq Y (k + 1) ω| ∂P ≤ 4 * BurkholderDFI.SquareFnLp.pNorm P 1 f ∧
      P {ω | 0 < BurkholderDFI.SquareFnLp.maxFn Z ω} ≤ BurkholderDFI.SquareFnLp.pNorm P 1 f / ENNReal.ofReal l := by sorry

end BurkholderDFI.Gundy
