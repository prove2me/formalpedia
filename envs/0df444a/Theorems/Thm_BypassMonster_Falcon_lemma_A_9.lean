-- Prove2me | Theorems.Thm_BypassMonster_Falcon_lemma_A_9
-- name    : BypassMonster.Falcon.lemma_A_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:47.304224+00:00
-- url     : https://prove2.me/theorems/4f2b7f77-3e12-44a9-8068-f9ebe179ab68
-- title:
--   Lemma A.9, p. 1927 (Setup 2) — on Γ₂, Σ_π Qₘ(π) Reg(π) ≤ 7.15K/γₘ
-- statement:
--   Consider Setup 2 with epoch horizon $M$ and an outcome in the event $\Gamma_2$. For every epoch $1\le m\le M$,
--   $$\sum_{\pi\in\Psi}Q_m(\pi)\,\mathrm{Reg}(\pi)\le\frac{7.15\,K}{\gamma_m}.$$
--
--   By Lemma A.4 the left side is the expected instantaneous regret of every round of epoch $m$, so this is the per-round regret bound that Lemma A.10 sums.
--
--   **Formalization Note** Setup 2 branch of a lemma stated for Setups 1 and 2. $7.15=2+c_0$ with $c_0=5.15$. Finite $\mathcal X$, $[0,1]$ rewards.
-- source:
--   Simchi-Levi & Xu, Math. Oper. Res. 47(3) (2022), Lemma A.9 and its proof, p. 1927

import Mathlib
import Definitions.Def_BypassMonster_Falcon_Model
import Definitions.Def_BypassMonster_Falcon_Analysis

namespace BypassMonster.Falcon

open MeasureTheory ProbabilityTheory

/-- **Lemma A.9** (p. 1927), Setup 2 branch: on `Γ_2`, for every epoch `1 ≤ m ≤ M`,
`∑_{π ∈ Ψ} Q_m(π) Reg(π) ≤ 7.15 K/γ_m`. -/
theorem lemma_A_9
    {X : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    {K : ℕ} [NeZero K]
    (DX : Measure X) [IsProbabilityMeasure DX]
    (ν : Kernel X (Fin K → ℝ)) [IsMarkovKernel ν]
    (A : Params X K) (πstar : X → Fin K)
    (M : ℕ) (hS : Setup2 DX ν A πstar M) (ω : Params.Omega X K) (hω : ω ∈ A.Gamma2 DX ν)
    (m : ℕ) (hm : 1 ≤ m) (hmM : m ≤ M) :
    ∑ π : X → Fin K, A.Qm m ω π * Reg DX ν πstar π ≤ 715 / 100 * (K : ℝ) / A.gamma m := by sorry

end BypassMonster.Falcon
