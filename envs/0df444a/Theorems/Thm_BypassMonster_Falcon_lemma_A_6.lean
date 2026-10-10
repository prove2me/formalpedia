-- Prove2me | Theorems.Thm_BypassMonster_Falcon_lemma_A_6
-- name    : BypassMonster.Falcon.lemma_A_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:30.452932+00:00
-- url     : https://prove2.me/theorems/13ca0c2a-c02d-45c4-9991-666e9c2f0f48
-- title:
--   Lemma A.6, p. 1924 — V(pₘ, π) ≤ K + γₘ Reĝ(π)
-- statement:
--   For every epoch $m\ge1$, every outcome of the run and every deterministic policy $\pi\in\Psi$,
--   $$V(p_m,\pi)=\mathbb E_{x\sim\mathcal D_{\mathcal X}}\Big[\frac{1}{p_m(\pi(x)\mid x)}\Big]\le K+\gamma_m\,\widehat{\mathrm{Reg}}_m(\pi).$$
--
--   The left side measures how far the algorithm's randomization in epoch $m$ is from following $\pi$; the lemma bounds it by the predicted regret of $\pi$.
--
--   **Formalization Note** The only hypotheses are that $\mathcal D_{\mathcal X}$ is a probability measure on the finite context set and that the tie-breaking rule picks a maximizer. The proof's step "$1/(1/K)=K$" for the greedy action is read as $p_m(\hat a_m(x)\mid x)\ge 1/K$.
-- source:
--   Simchi-Levi & Xu, Math. Oper. Res. 47(3) (2022), Lemma A.6 and its proof, p. 1924

import Mathlib
import Definitions.Def_BypassMonster_Falcon_Model
import Definitions.Def_BypassMonster_Falcon_Analysis

namespace BypassMonster.Falcon

open MeasureTheory

/-- **Lemma A.6** (p. 1924): for every epoch `m ≥ 1`, outcome `ω` and policy `π ∈ Ψ`,
`V(p_m, π) ≤ K + γ_m Reĝ(π)`, where `Reĝ` is the predicted implicit regret of epoch `m`. -/
theorem lemma_A_6
    {X : Type*} [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    {K : ℕ} [NeZero K]
    (DX : Measure X) [IsProbabilityMeasure DX]
    (A : Params X K) (hamax : ∀ (g : Fin K → ℝ) (a : Fin K), g a ≤ g (A.amax g))
    (m : ℕ) (hm : 1 ≤ m) (ω : Params.Omega X K) (π : X → Fin K) :
    V DX (A.pm m ω) π ≤ (K : ℝ) + A.gamma m * A.RegHat DX m ω π := by sorry

end BypassMonster.Falcon
