-- Prove2me | Theorems.Thm_Avram2004_Russian_stopped_value_martingale
-- name    : Avram2004.Russian.stopped_value_martingale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:10:50.824222+00:00
-- url     : https://prove2.me/theorems/066eb369-08ec-4fd2-8005-634248a778f7
-- title:
--   §6, proof of Theorem 2 (p. 230) — the stopped process e^{−α(t∧τ_κ*)} u(Y_{t∧τ_κ*}) is a ℙ¹-martingale
-- statement:
--   Let $X$ be a spectrally negative Lévy process with respect to a right-continuous filtration $\mathbf F$ on $(\Omega,\mathcal F,\mathbb P)$, satisfying the standing assumption (unbounded variation, or bounded variation and $\Lambda(dx)\ll dx$), with Laplace exponent $\psi$. Let $r\ge0$ with $\psi(1)=r$, let $\mathbb P^1$ be the Esscher measure, $d\mathbb P^1/d\mathbb P|_{\mathcal F_t}=e^{X_t-rt}$, let $\alpha>0$ and $q=\alpha+r$. Write $W^{(q)}$, $Z^{(q)}$ for the scale functions of $(X,\mathbb P)$ and, for $z\ge0$, let $Y$ be the reflected process under $\mathbb P^1_{-z}$ (so $Y_0=z$). Let $\kappa^*$ be given by (30) and $u(y)=e^{y}Z^{(q)}(\kappa^*-y)$ as in Theorem 2. Then the process
--   $$e^{-\alpha(t\wedge\tau_{\kappa^*})}\,u\big(Y_{t\wedge\tau_{\kappa^*}}\big),\qquad t\ge0,$$
--   is a martingale under $\mathbb P^1$ with respect to $\mathbf F$.
--
--   This is the martingale half of the verification argument: on the continuation region $[0,\kappa^*)$ the candidate value $u$ is harmonic for the discounted reflected process, which yields equality at $\tau_{\kappa^*}$.
--
--   **Formalization Note** The paper states this in the unbounded-variation case of the proof ("From Remark 6 we know that …") and says that the other cases follow "exactly the same line of reasoning"; it is stated here under the standing assumption, covering all cases (when $\kappa^*=0$ the process is constant). The martingale property includes adaptedness, as in Mathlib's `Martingale`. The encoding $\mathbb P^1_{-z}$ (prior maximum $0$, start $-z$) gives the same reflected process as the paper's $\mathbb P^1_{s,x}$ with $s-x=z$. The hypotheses are those of Theorem 2: the filtration is right-continuous but not completed, and "$\psi(1)=r$" is Mathlib's cumulant generating function at $1$; integrability of $e^{X_1}$ is not added, since the Esscher relation at $t=1$ already forces $\mathbb E[e^{X_1-r}]=1$.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 230, §6, proof of Theorem 2, sentence after (31) ("From Remark 6 we know that …"); Remark 6, p. 225

import Mathlib
import Definitions.Def_Avram2004_Shared_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale
import Definitions.Def_Avram2004_Shared_reflected
import Definitions.Def_Avram2004_Shared_esscher
import Definitions.Def_Avram2004_Russian_russianProblem

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Avram2004.Russian

/-- §6, proof of Theorem 2, p. 230 (sentence after (31)): under `ℙ^1_{-z}` (`Y = refl 0 (-z) X`,
`Y_0 = z ≥ 0`), with `u` as in Theorem 2 and `q = α + r`, the stopped process
`exp{-α(t ∧ τ_{κ*})} u(Y_{t ∧ τ_{κ*}})`, `t ≥ 0`, is a `Q`-martingale with respect to `𝓕`. -/
theorem stopped_value_martingale {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r α q : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (hα : 0 < α) (hq : q = α + r)
    (z : ℝ) (hz : 0 ≤ z) :
    Martingale
      (fun (t : ℝ≥0) ω =>
        Real.exp (-α * (Shared.stopAt t (Shared.tau 0 (-z) X (kappaStar P X q) ω) : ℝ))
          * uR P X q (Shared.refl 0 (-z) X (Shared.stopAt t (Shared.tau 0 (-z) X (kappaStar P X q) ω)) ω))
      𝓕 Q := by sorry

end Avram2004.Russian
