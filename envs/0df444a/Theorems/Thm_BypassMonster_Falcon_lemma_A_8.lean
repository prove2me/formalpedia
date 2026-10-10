-- Prove2me | Theorems.Thm_BypassMonster_Falcon_lemma_A_8
-- name    : BypassMonster.Falcon.lemma_A_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:38.628813+00:00
-- url     : https://prove2.me/theorems/b57bf5d5-f544-4ba8-a557-8456e88e47d4
-- title:
--   Lemma A.8, p. 1925 (Setup 2) — on Γ₂, Reg(π) ≤ 2Reĝ(π) + c₀K/γₘ and Reĝ(π) ≤ 2Reg(π) + c₀K/γₘ, c₀ = 5.15
-- statement:
--   Consider Setup 2 with epoch horizon $M$ and an outcome in the event $\Gamma_2$. Let $c_0=5.15$. For every epoch $1\le m\le M$ and every policy $\pi\in\Psi$,
--   $$\mathrm{Reg}(\pi)\le 2\,\widehat{\mathrm{Reg}}_m(\pi)+\frac{c_0K}{\gamma_m},\qquad \widehat{\mathrm{Reg}}_m(\pi)\le 2\,\mathrm{Reg}(\pi)+\frac{c_0K}{\gamma_m}.$$
--
--   The true and predicted implicit regrets are equivalent up to a factor $2$ and an additive $O(K/\gamma_m)$ that shrinks as epochs progress; this is what lets the algorithm's predicted-regret control (Lemma A.5) transfer to the true regret.
--
--   **Formalization Note** Setup 2 branch of a lemma stated for Setups 1 and 2. The page's base case uses Condition (5); with $[0,1]$ rewards it holds automatically. The monotonicity $\gamma_1\le\dots\le\gamma_M$ assumed in Setup 2 is used, which is why the epoch is bounded by $M$. (A.8) in the proof prints $\sqrt{\mathcal V_t(\pi)}\sqrt K/\gamma_m$ without the $2$ of Lemma A.7; the statement is unaffected.
-- source:
--   Simchi-Levi & Xu, Math. Oper. Res. 47(3) (2022), Lemma A.8 and its proof, pp. 1925–1927

import Mathlib
import Definitions.Def_BypassMonster_Falcon_Model
import Definitions.Def_BypassMonster_Falcon_Analysis

namespace BypassMonster.Falcon

open MeasureTheory ProbabilityTheory

/-- **Lemma A.8** (p. 1925), Setup 2 branch: on `Γ_2`, with `c_0 = 5.15`, for every epoch
`1 ≤ m ≤ M` and every policy `π ∈ Ψ`, `Reg(π) ≤ 2 Reĝ(π) + c_0 K/γ_m` and
`Reĝ(π) ≤ 2 Reg(π) + c_0 K/γ_m`, with `Reĝ` the predicted implicit regret of epoch `m`. -/
theorem lemma_A_8
    {X : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    {K : ℕ} [NeZero K]
    (DX : Measure X) [IsProbabilityMeasure DX]
    (ν : Kernel X (Fin K → ℝ)) [IsMarkovKernel ν]
    (A : Params X K) (πstar : X → Fin K)
    (M : ℕ) (hS : Setup2 DX ν A πstar M) (ω : Params.Omega X K) (hω : ω ∈ A.Gamma2 DX ν)
    (m : ℕ) (hm : 1 ≤ m) (hmM : m ≤ M) (π : X → Fin K) :
    Reg DX ν πstar π ≤ 2 * A.RegHat DX m ω π + 515 / 100 * (K : ℝ) / A.gamma m ∧
    A.RegHat DX m ω π ≤ 2 * Reg DX ν πstar π + 515 / 100 * (K : ℝ) / A.gamma m := by sorry

end BypassMonster.Falcon
