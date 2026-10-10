-- Prove2me | Theorems.Thm_BypassMonster_Falcon_lemma_A_4
-- name    : BypassMonster.Falcon.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:37.589389+00:00
-- url     : https://prove2.me/theorems/1fd6ceab-657f-46c4-9386-ffb61027fa0b
-- title:
--   Lemma A.4, p. 1923 — E[rₜ(π_{f*}(xₜ)) − rₜ(aₜ) | past] = Σ_π Q_{m(t)}(π) Reg(π)
-- statement:
--   Consider Setup 2 and a round $t\ge1$, in epoch $m(t)$. The instantaneous regret $r_t(\pi_{f^*}(x_t))-r_t(a_t)$ is integrable, and its conditional expectation given the past equals the implicit regret of the randomized policy $Q_{m(t)}$:
--   $$\mathbb E\big[r_t(\pi_{f^*}(x_t))-r_t(a_t)\ \big|\ \mathcal F_{t-1}\big]=\sum_{\pi\in\Psi}Q_{m(t)}(\pi)\,\mathrm{Reg}(\pi)\quad\text{almost surely}.$$
--
--   It reduces the analysis of the algorithm's expected regret to the implicit regret of the induced randomized policies.
--
--   **Formalization Note** $\mathcal F_{t-1}=\sigma(\omega_0,\dots,\omega_{t-1})$ is the coordinate filtration of the canonical space, which contains the paper's $\Upsilon_{t-1}=\sigma((x_1,r_1,a_1),\dots,(x_{t-1},r_{t-1},a_{t-1}))$. The page's "$r_t(\pi_{f^*})$" is $r_t(\pi_{f^*}(x_t))$. Integrability is stated as a conjunct so the conditional expectation is not a junk value. Finite $\mathcal X$, $[0,1]$ rewards and the measurability hypotheses are part of `Setup2`.
-- source:
--   Simchi-Levi & Xu, Math. Oper. Res. 47(3) (2022), Lemma A.4 and its proof, p. 1923

import Mathlib
import Definitions.Def_BypassMonster_Falcon_Model
import Definitions.Def_BypassMonster_Falcon_Analysis

namespace BypassMonster.Falcon

open MeasureTheory ProbabilityTheory

/-- **Lemma A.4** (p. 1923): for every round `t ≥ 1` (in epoch `m(t)`), the conditional expected
instantaneous regret given the past equals the implicit regret of the randomized policy `Q_{m(t)}`:
`E[r_t(π_{f*}(x_t)) − r_t(a_t) | ℱ_{t−1}] = ∑_{π ∈ Ψ} Q_{m(t)}(π) Reg(π)` almost surely, where
`ℱ_{t−1} = σ(ω 0, …, ω (t−1))` is the coordinate filtration of the canonical space (it contains
`Υ_{t−1}`). The instantaneous regret is integrable. -/
theorem lemma_A_4
    {X : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    {K : ℕ} [NeZero K]
    (DX : Measure X) [IsProbabilityMeasure DX]
    (ν : Kernel X (Fin K → ℝ)) [IsMarkovKernel ν]
    (A : Params X K) (πstar : X → Fin K)
    (M : ℕ) (hS : Setup2 DX ν A πstar M) (t : ℕ) (ht : 1 ≤ t) :
    Integrable (fun ω : Params.Omega X K => (ω t).1.2 (πstar (ω t).1.1) - (ω t).1.2 (A.action t ω))
        (canonMeasure DX ν) ∧
    (canonMeasure DX ν)[fun ω : Params.Omega X K =>
          (ω t).1.2 (πstar (ω t).1.1) - (ω t).1.2 (A.action t ω)
        | Filtration.piLE (X := fun _ : ℕ => (X × (Fin K → ℝ)) × unitInterval) (t - 1)]
      =ᵐ[canonMeasure DX ν]
        fun ω => ∑ π : X → Fin K, A.Qm (epochOf A.τ t) ω π * Reg DX ν πstar π := by sorry

end BypassMonster.Falcon
