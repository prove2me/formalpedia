-- Prove2me | Theorems.Thm_BurkholderDFI_Gundy_doob_stopped_L1
-- name    : BurkholderDFI.Gundy.doob_stopped_L1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:40.282759+00:00
-- url     : https://prove2.me/theorems/6d2ae0db-200e-4de4-80cf-db8882eea049
-- title:
--   Doob (cited in §1): an L¹-bounded martingale converges a.e., and ‖f_μ‖₁ ≤ ‖f‖₁ for every stopping time μ
-- statement:
--   Let $f=(f_1,f_2,\dots)$ be a martingale, or a nonnegative submartingale, relative to $\mathcal A_1,\mathcal A_2,\dots$ on a probability space $(\Omega,\mathcal A,P)$, and suppose $f$ is $L^1$-bounded: $\|f\|_1=\sup_{n\ge1}E|f_n|<\infty$. Let $\mu$ be a stopping time with values in $\{0,1,2,\dots,\infty\}$. Then $f_n$ converges almost everywhere to a limit $f_\infty$, and
--   $$\|f_\mu\|_1=E|f_\mu|\le\|f\|_1,$$
--   where $f_\mu(\omega)=f_{\mu(\omega)}(\omega)$, with $f_\infty$ on $\{\mu=\infty\}$ and $f_0=0$ on $\{\mu=0\}$.
--
--   Burkholder quotes these two facts from Doob's *Stochastic Processes* and uses them throughout; in Gundy's decomposition they bound the integral of $|f_\mu|$ over $\{\mu<\infty\}$ by $\|f\|_1$.
--
--   **Formalization Note** The paper's martingale (or nonnegative submartingale) is indexed from $1$; Lean's process also has an index $0$, constrained by Mathlib's definition ($f_0=E(f_1\mid\mathcal A_0)$, resp. $\le$). This is no restriction: every process of the paper extends to one of Mathlib's by setting $f_0:=E(f_1\mid\mathcal A_0)$. The paper's "nonnegative" is read as $f_n\ge0$ almost surely for $n\ge1$. The conclusion asserts the existence of a function $f_\infty$ to which $f_n$ converges almost everywhere and for which the bound holds; since two almost-everywhere limits agree almost everywhere, the bound holds for every such limit. Norms are computed in $[0,\infty]$.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §1, p. 20 (citing Doob [15])

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.Gundy

/-- §1, p. 20 (cited from Doob): if `f` is an `L¹`-bounded martingale or nonnegative submartingale
and `μ` is a stopping time, then `f` converges almost everywhere and `‖f_μ‖₁ ≤ ‖f‖₁`
(with `f_∞` the a.e. limit on `{μ = ∞}`). -/
theorem doob_stopped_L1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (hL1 : BurkholderDFI.SquareFnLp.pNorm P 1 f < ⊤) (μ : Ω → ℕ∞) (hμ : IsStoppingTime ℱ μ) :
    ∃ fInf : Ω → ℝ, (∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (fInf ω))) ∧
      ∫⁻ ω, ENNReal.ofReal |BurkholderDFI.SquareFnLp.valAt f fInf (μ ω) ω| ∂P ≤ BurkholderDFI.SquareFnLp.pNorm P 1 f := by sorry

end BurkholderDFI.Gundy
