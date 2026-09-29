-- Prove2me | Theorems.Thm_Avram2004_Exit_mgf_eq_exp_psi
-- name    : Avram2004.Exit.mgf_eq_exp_psi
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:20:32.695432+00:00
-- url     : https://prove2.me/theorems/feb9ba08-2533-43d8-a2cd-adfbb479a276
-- title:
--   Eq. (2) — 𝔼[e^{θX_t}] = e^{tψ(θ)}
-- statement:
--   Let $X$ be a spectrally negative Lévy process on $(\Omega,\mathcal F,\mathbb P)$ satisfying the paper's standing assumption, and let $\psi(\theta)=\log\mathbb E[e^{\theta X_1}]$ be its Laplace exponent. For every $t\ge0$ and every real $\theta$ such that $e^{\theta X_t}$ is integrable,
--   $$\mathbb E\big[e^{\theta X_t}\big]=e^{t\psi(\theta)} .$$
--
--   This is the property that makes $\psi$ the exponent of the whole process and not only of $X_1$; it underlies the Esscher martingales $\exp(cX_t-\psi(c)t)$ and the tilted exponents $\psi_c$.
--
--   **Formalization Note** "When the moment generating function of the process at time $t$ exists" is read as integrability of $e^{\theta X_t}$. For $t>0$ this implies integrability of $e^{\theta X_1}$, so $\psi(\theta)$ is the genuine logarithm. The standing assumption is carried as in every statement of the paper, although this identity does not need it.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 216, Eq. (2)

import Mathlib
import Definitions.Def_Avram2004_Exit_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Avram2004.Exit

/-- (2), p. 216: whenever the moment generating function of `X_t` exists at `θ`,
`𝔼[e^{θX_t}] = e^{tψ(θ)}` with `ψ(θ) = log 𝔼[e^{θX_1}]`. -/
theorem mgf_eq_exp_psi {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsSNLevy P X) (hS : Shared.Standing P X)
    (t : ℝ≥0) (θ : ℝ) (hint : Integrable (fun ω => Real.exp (θ * X t ω)) P) :
    ∫ ω, Real.exp (θ * X t ω) ∂P = Real.exp ((t : ℝ) * Shared.psi P X θ) := by sorry

end Avram2004.Exit
