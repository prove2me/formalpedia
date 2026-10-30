-- Prove2me | Theorems.Thm_CPDETrial_prop3_ui_martingale
-- name    : CPDETrial.prop3_ui_martingale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:54:38.163162+00:00
-- url     : https://prove2.me/theorems/c081d280-7c09-4e51-b967-b6a0d76fae2e
-- title:
--   Prop. 3 — $Z^\tau_i$ is a uniformly integrable martingale
-- statement:
--   Fix an arm $i$ with sampling variance $\lambda_i>0$ and current posterior variance $\Sigma^t_{i,i}>0$, and let $Z^\tau_i=\mu^{t+\tau}_i-\mu^t_i$ be the change of the mean belief after $\tau$ further observations of arm $i$, under the predictive law. Then:
--
--   1. $(Z^\tau_i)_{\tau\ge0}$ is a martingale for its own filtration;
--   2. the family $(Z^\tau_i)_{\tau\ge0}$ is uniformly integrable;
--   3. for every almost surely finite stopping time $T_i$ of this filtration,
--   $$
--   \mathbb E\big[Z^{T_i}_i\,\big|\,\mu^t,\Sigma^t\big]=0 .
--   $$
--
--   This is what allows the term $\mathbb E[b_{g(0)}Z^{T_i}_i]$ to be dropped when the cPDE index is simplified.
--
--   Differences from the source:
--   - reading: for any stopping time T_i → for every stopping time of the natural filtration of Z that is finite almost surely; reason: Z^{T_i} is undefined on {T_i = ∞}; the paper only uses finite stopping times
--   - encoding: E_{T_i}[Z^{T_i}_i | µ^t,Σ^t] → integral of the stopped process under the canonical predictive law, with λ_i, Σ^t_ii as parameters; reason: conditioning on the current belief fixes these parameters
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. 12, Prop. 3 (proof p. ec3, App. B.3)

import Mathlib
import Definitions.Def_CPDETrial_zProc
import Definitions.Def_CPDETrial_zFilt
import Definitions.Def_CPDETrial_idxP
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **Prop. 3 — `Z^τ_i` is a uniformly integrable martingale; optional stopping.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), Prop. 3, p. 12 (proof: App. B.3, p. ec3):
"`Z^τ_i` is a uniformly integrable martingale. `E_{T_i}[Z^{T_i}_i | µ^t,Σ^t] = 0` for any stopping
time `T_i`."

For a sampling variance `l = λ_i > 0` and a current variance `s = Σ^t_{i,i} > 0`, under the
predictive law `idxP`:
1. `τ ↦ Z^τ = zProc l s τ` is a martingale for its natural filtration `zFilt l s`;
2. the family `(Z^τ)_τ` is uniformly integrable;
3. `E[Z^T] = 0` for every stopping time `T` of `zFilt l s` that is finite almost surely.

**Formalization Note.** "any stopping time" is read as any almost surely finite stopping time:
`Z^T` is undefined on `{T = ∞}` and the paper only uses finite `T`. Stopping times are
`WithTop ℕ`-valued; `stoppedValue` evaluates `Z` at `T` (at `0` on the null set `{T = ⊤}`). -/
theorem prop3_ui_martingale (l : ℝ≥0) (s : ℝ) (hl : 0 < l) (hs : 0 < s) :
    Martingale (fun τ => zProc l s τ) (zFilt l s) idxP ∧
    UniformIntegrable (fun τ => zProc l s τ) 1 idxP ∧
    ∀ T : (ℕ → ℝ) → WithTop ℕ, IsStoppingTime (zFilt l s) T → (∀ᵐ ω ∂idxP, T ω ≠ ⊤) →
      ∫ ω, stoppedValue (fun τ => zProc l s τ) T ω ∂idxP = 0 := by sorry

end CPDETrial
