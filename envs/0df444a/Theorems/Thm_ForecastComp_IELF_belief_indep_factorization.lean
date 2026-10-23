-- Prove2me | Theorems.Thm_ForecastComp_IELF_belief_indep_factorization
-- name    : ForecastComp.IELF.belief_indep_factorization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:37.596209+00:00
-- url     : https://prove2.me/theorems/e04d9edc-fe75-477c-8523-5e27db01f536
-- title:
--   Proof of Theorem 6 (Appendix L), p. 34 — under belief independence the event lotteries F_k are independent
-- statement:
--   Let $n\ge2$, let $R$ take values in $[0,1]$ on $[0,1]$ and be measurable in the report, and let $D=\nu_1\otimes\cdots\otimes\nu_m$ be a belief-independent joint law: each $\nu_k$ is a probability law of the pair (outcome $X_k$, reports $Y_{\cdot,k}$ on event $k$), with reports in $[0,1]$ almost surely, and the pairs are independent across events. Fix a forecaster $i$ and a report vector $y_i\in[0,1]^m$. For every event $k$ and forecaster $l$ let
--   $$\bar q_{k,l}=\mathbb E_{\nu_k}\big[f_{l,k}(Y_{1,k},\dots,y_{i,k},\dots,Y_{n,k},X_k)\big]$$
--   be $l$'s expected ELF winning probability on event $k$. Then the probability that I-ELF selects $i$ is the most-wins selection probability computed from these expected lotteries:
--   $$\Pr_{D}\big(M_{\text{I-ELF}^R}(Y_1,\dots,y_i,\dots,Y_n,X)=i\big)=\mathrm{winProb}(\bar q,i),$$
--   where $\mathrm{winProb}(q,i)$ is the probability that $i$ is selected (most wins, uniform tie-breaking) when the event winners are drawn independently with $\Pr(w_k=l)=q_{k,l}$.
--
--   This is the first step of the proof of Theorem 6: under belief independence, forecaster $i$ can reason about each event separately.
--
--   **Formalization Note** $D$ is `Measure.pi ν`; the $i$-th report coordinate of each sample is overwritten by $y_i$.
-- source:
--   Witkowski et al., arXiv:2101.01816v2, p. 34, proof of Theorem 6 (Appendix L), first paragraph

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

namespace ForecastComp.IELF

open MeasureTheory

/-- Proof of Theorem 6 (Appendix L), p. 34: under belief independence the selection probability
of I-ELF factorises — it is the most-wins winning probability computed from the expected event
lotteries `E[F_k]`. -/
theorem belief_indep_factorization {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ)
    (hbdd : IsUnitBounded R) (hmeas : ∀ x, Measurable (fun y => R y x))
    (ν : Fin m → Measure (Bool × (Fin n → ℝ))) [∀ k, IsProbabilityMeasure (ν k)]
    (hrep : ∀ k, ∀ᵐ b ∂(ν k), ∀ j, b.2 j ∈ Set.Icc (0:ℝ) 1)
    (i : Fin n) (yi : Fin m → ℝ) (hyi : ∀ k, yi k ∈ Set.Icc (0:ℝ) 1) :
    ∫ ω, ielfSelProb R (Function.update (reportsOf ω) i yi) (outcomeOf ω) i ∂(Measure.pi ν) =
      winProbOf (fun k l => ∫ b, elfProb R (Function.update b.2 i (yi k)) b.1 l ∂(ν k)) i := by sorry

end ForecastComp.IELF
