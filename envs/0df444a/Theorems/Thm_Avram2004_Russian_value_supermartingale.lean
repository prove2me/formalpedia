-- Prove2me | Theorems.Thm_Avram2004_Russian_value_supermartingale
-- name    : Avram2004.Russian.value_supermartingale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:12:22.331019+00:00
-- url     : https://prove2.me/theorems/553d3b03-90ba-4567-a3e5-fa77b52f48d1
-- title:
--   §6, proof of Theorem 2 (p. 230) — e^{−αt} u(Y_t) is a ℙ¹-supermartingale
-- statement:
--   Let $X$ be a spectrally negative Lévy process with respect to a right-continuous filtration $\mathbf F$ on $(\Omega,\mathcal F,\mathbb P)$, satisfying the standing assumption (unbounded variation, or bounded variation and $\Lambda(dx)\ll dx$), with Laplace exponent $\psi$. Let $r\ge0$ with $\psi(1)=r$, let $\mathbb P^1$ be the Esscher measure, $d\mathbb P^1/d\mathbb P|_{\mathcal F_t}=e^{X_t-rt}$, let $\alpha>0$ and $q=\alpha+r$. Write $W^{(q)}$, $Z^{(q)}$ for the scale functions of $(X,\mathbb P)$ and, for $z\ge0$, let $Y$ be the reflected process under $\mathbb P^1_{-z}$ (so $Y_0=z$). Let $\kappa^*$ be given by (30) and $u(y)=e^{y}Z^{(q)}(\kappa^*-y)$. Then
--   $$\big(e^{-\alpha t}\,u(Y_t)\big)_{t\ge0}$$
--   is a supermartingale under $\mathbb P^1$ with respect to $\mathbf F$: each $e^{-\alpha t}u(Y_t)$ is $\mathcal F_t$-measurable and $\mathbb P^1$-integrable, and $\mathbb E^1[e^{-\alpha t}u(Y_t)\mid\mathcal F_s]\le e^{-\alpha s}u(Y_s)$ almost surely for $s\le t$.
--
--   Combined with optional stopping and $e^{y}\le u(y)$, this gives the upper bound $\mathbb E^1_{-z}[e^{-\alpha\tau+Y_\tau}]\le u(z)$ for every admissible $\tau$.
--
--   **Formalization Note** Mathlib's `Supermartingale` includes adaptedness and integrability. The page states it for $\mathbb P^1_{s,x}$; with $z=s-x$ this is the same reflected process. The page proves it in each of the three cases of the proof separately; the statement here covers all of them under the standing assumption. The hypotheses are those of Theorem 2: the filtration is right-continuous but not completed, and "$\psi(1)=r$" is Mathlib's cumulant generating function at $1$; integrability of $e^{X_1}$ is not added, since the Esscher relation at $t=1$ already forces $\mathbb E[e^{X_1-r}]=1$.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 230, §6, proof of Theorem 2 ("An argument similar to the one presented in Remark 5 now shows that exp{−αt}u(Y_t) is a ℙ¹_{s,x}-supermartingale"); p. 231 for the bounded-variation cases

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

/-- §6, proof of Theorem 2, p. 230: under `ℙ^1_{-z}` (`Y = refl 0 (-z) X`, `Y_0 = z ≥ 0`), with `u` as in
Theorem 2 and `q = α + r`, the process `exp{-αt} u(Y_t)`, `t ≥ 0`, is a `Q`-supermartingale with
respect to `𝓕` (each `exp{-αt} u(Y_t)` being `Q`-integrable). -/
theorem value_supermartingale {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r α q : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (hα : 0 < α) (hq : q = α + r)
    (z : ℝ) (hz : 0 ≤ z) :
    Supermartingale (fun (t : ℝ≥0) ω => Real.exp (-α * (t : ℝ)) * uR P X q (Shared.refl 0 (-z) X t ω)) 𝓕 Q := by sorry

end Avram2004.Russian
