-- Prove2me | Theorems.Thm_BypassMonster_Falcon_lemma_A_2
-- name    : BypassMonster.Falcon.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:26.545952+00:00
-- url     : https://prove2.me/theorems/efe7140a-9705-40ac-a515-ea1036e94b94
-- title:
--   Lemma A.2, pp. 1922–1923 — w.p. ≥ 1−δ/(2m²) the error of f̂ₘ is ≤ ℰ_{ℱ,δ/(2m²)}(τₘ₋₁−τₘ₋₂) = K/(4γₘ²); Γ₂ holds w.p. ≥ 1−δ/2
-- statement:
--   Consider Setup 2 and the run of FALCON+ with confidence parameter $\delta$. For an epoch $m\ge2$ let
--   $$\mathrm{err}_m=\mathbb E_{x\sim\mathcal D_{\mathcal X},\,a\sim p_{m-1}(\cdot\mid x)}\big[(\hat f_m(x,a)-f^*(x,a))^2\big]$$
--   be the error of the predictor $\hat f_m$ under the kernel $p_{m-1}$ that generated its training data (epoch $m-1$). Then:
--
--   1. for every $m\ge2$, with probability at least $1-\delta/(2m^2)$,
--   $$\mathrm{err}_m\le\frac{K}{4\gamma_m^2},\qquad\text{and}\qquad \mathcal E_{\mathcal F,\delta/(2m^2)}(\tau_{m-1}-\tau_{m-2})=\frac{K}{4\gamma_m^2};$$
--   2. consequently (union bound) the event $\Gamma_2=\{\forall m\ge2:\ \mathrm{err}_m\le K/(4\gamma_m^2)\}$ holds with probability at least $1-\delta/2$.
--
--   This is the reduction from the bandit problem to offline regression: because each oracle call uses only the data of the previous epoch, which are i.i.d. given the past, Assumption 2 applies to every call.
--
--   **Formalization Note** Probabilities are stated in failure form on the canonical space: the failure set has outer measure at most $\delta/(2m^2)$, resp. $\delta/2$. The printed conditional expectation $\mathbb E_{x_t,a_t}[\cdot\mid\Upsilon_{t-1}]$ is encoded as $\mathrm{err}_m$, following the rewriting in the paper's proof; the printed $\Gamma_2$ ("$t$ in epoch $m$") and the proof's "$a_t\sim p_{m(t)-1}$" are read as epoch $m-1$ and kernel $p_{m-1}$. Finite $\mathcal X$, $[0,1]$ rewards (Condition (5)'s heavy-tailed generality is not formalized), and the added hypotheses $\mathcal E>0$ and measurability of the oracle and tie-breaking rule, all part of `Setup2`.
-- source:
--   Simchi-Levi & Xu, Math. Oper. Res. 47(3) (2022), Lemma A.2 and its proof, pp. 1922–1923

import Mathlib
import Definitions.Def_BypassMonster_Falcon_Model
import Definitions.Def_BypassMonster_Falcon_Analysis

namespace BypassMonster.Falcon

open MeasureTheory ProbabilityTheory

/-- **Lemma A.2** (pp. 1922–1923): under Setup 2, for every epoch `m ≥ 2`, with probability at
least `1 − δ/(2m²)` the error of `f̂_m` under the kernel `p_{m−1}` of its training epoch is at most
`ℰ_{ℱ,δ/(2m²)}(τ_{m−1} − τ_{m−2}) = K/(4γ_m²)`; and (union bound) the event `Γ_2` holds with probability
at least `1 − δ/2`. Stated in failure form. -/
theorem lemma_A_2
    {X : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    {K : ℕ} [NeZero K]
    (DX : Measure X) [IsProbabilityMeasure DX]
    (ν : Kernel X (Fin K → ℝ)) [IsMarkovKernel ν]
    (A : Params X K) (πstar : X → Fin K)
    (M : ℕ) (hS : Setup2 DX ν A πstar M) :
    (∀ m : ℕ, 2 ≤ m →
      canonMeasure DX ν {ω | (K : ℝ) / (4 * A.gamma m ^ 2) < A.errSq DX ν m ω}
          ≤ ENNReal.ofReal (A.δ / (2 * (m : ℝ) ^ 2)) ∧
        A.E (A.δ / (2 * (m : ℝ) ^ 2)) (A.τ (m - 1) - A.τ (m - 2)) = (K : ℝ) / (4 * A.gamma m ^ 2)) ∧
    canonMeasure DX ν (A.Gamma2 DX ν)ᶜ ≤ ENNReal.ofReal (A.δ / 2) := by sorry

end BypassMonster.Falcon
