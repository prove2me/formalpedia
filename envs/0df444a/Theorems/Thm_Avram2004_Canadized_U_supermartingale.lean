-- Prove2me | Theorems.Thm_Avram2004_Canadized_U_supermartingale
-- name    : Avram2004.Canadized.U_supermartingale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:42:14.048991+00:00
-- url     : https://prove2.me/theorems/92562e40-1da0-499f-98e6-8a5d718651e1
-- title:
--   §7, proof of Theorem 3 — U_t = e^{−(α+λ)t}h(Y_t) + λ∫_0^t e^{−(α+λ)u+Y_u}du is a ℙ¹-supermartingale
-- statement:
--   Let $X$ be a spectrally negative Lévy process with respect to a right-continuous filtration $\mathbf F=\{\mathcal F_t\}_{t\ge0}$ under $\mathbb P$, satisfying the paper's standing assumption (unbounded variation, or bounded variation and $\Lambda(dx)\ll dx$). Let $r\ge0$ with $\psi(1)=r$, where $\psi(\theta)=\log\mathbb E[e^{\theta X_1}]$ is the Laplace exponent, and let $\mathbb P^1$ be the Esscher measure, $d\mathbb P^1/d\mathbb P|_{\mathcal F_t}=e^{X_t-rt}$. Let $\alpha>0$, let $\eta(\lambda)$ be an exponential random variable of rate $\lambda>0$ which under $\mathbb P^1$ is independent of $\mathcal F_\infty=\bigvee_t\mathcal F_t$, and write $p=\alpha+\lambda+r$. $W^{(p)}$ and $Z^{(p)}(x)=1+p\int_{-\infty}^xW^{(p)}(y)\,dy$ are the scale functions of $(X,\mathbb P)$. Let $\kappa_*$ and $h$ be as in Theorem 3, and under $\mathbb P^1_{s,x}$ ($s-x\ge0$, $Y_0=s-x$) let
--   $$
--   U_t=e^{-(\alpha+\lambda)t}h(Y_t)+\lambda\int_0^te^{-(\alpha+\lambda)u+Y_u}\,du,\qquad t\ge0.
--   $$
--   Then $(U_t)_{t\ge0}$ is a $\mathbb P^1_{s,x}$-supermartingale with respect to $\mathbf F$.
--
--   This is the supermartingale half of the verification argument: by optional stopping it bounds the expected reward of every admissible rule by $h$.
--
--   **Formalization Note** The page derives the property in the case $W^{(p)}(0+)=0$ (unbounded variation) and states that the other cases $W^{(p)}(0+)\in(0,(p-\lambda)^{-1})$ and $W^{(p)}(0+)\ge(p-\lambda)^{-1}$ go the same way; the statement is made under the standing assumption, covering all cases. Supermartingale includes integrability and adaptedness (Mathlib's `Supermartingale`).
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 234, proof of Theorem 3 (last paragraph), with the other cases on p. 235

import Mathlib
import Definitions.Def_Avram2004_Shared_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale
import Definitions.Def_Avram2004_Shared_reflected
import Definitions.Def_Avram2004_Shared_esscher
import Definitions.Def_Avram2004_Canadized_canadizedProblem

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Avram2004.Canadized

/-- §7, proof of Theorem 3, p. 234: with `p = α + λ + r`, `h` as in Theorem 3 and, under `ℙ^1_{s,x}`
(`Y = refl s x X`, `s - x ≥ 0`), `U_t = e^{-(α+λ)t} h(Y_t) + λ ∫_0^t e^{-(α+λ)u+Y_u} du`, the process
`(U_t)_{t ≥ 0}` is a `Q`-supermartingale with respect to `𝓕`. -/
theorem U_supermartingale {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (α : ℝ) (hα : 0 < α) (η : Ω → ℝ) (lam : ℝ)
    (hη : IsExpClock 𝓕 Q η lam) (p : ℝ) (hp : p = α + lam + r)
    (s x : ℝ) (hsx : x ≤ s) :
    Supermartingale (fun (t : ℝ≥0) ω => U P X α lam p s x t ω) 𝓕 Q := by sorry

end Avram2004.Canadized
