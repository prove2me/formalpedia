-- Prove2me | Theorems.Thm_Avram2004_Canadized_lemma4_kappa_martingale
-- name    : Avram2004.Canadized.lemma4_kappa_martingale
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:34:06.488541+00:00
-- url     : https://prove2.me/theorems/b36b68a6-3d5e-4242-8ba2-6b6c18495667
-- title:
--   Lemma 4 (misprints corrected) — the level κ_* and the martingale property of U stopped at τ_{κ_*}
-- statement:
--   Let $X$ be a spectrally negative Lévy process with respect to a right-continuous filtration $\mathbf F=\{\mathcal F_t\}_{t\ge0}$ under $\mathbb P$, satisfying the paper's standing assumption (unbounded variation, or bounded variation and $\Lambda(dx)\ll dx$). Let $r\ge0$ with $\psi(1)=r$, where $\psi(\theta)=\log\mathbb E[e^{\theta X_1}]$ is the Laplace exponent, and let $\mathbb P^1$ be the Esscher measure, $d\mathbb P^1/d\mathbb P|_{\mathcal F_t}=e^{X_t-rt}$. Let $\alpha>0$, let $\eta(\lambda)$ be an exponential random variable of rate $\lambda>0$ which under $\mathbb P^1$ is independent of $\mathcal F_\infty=\bigvee_t\mathcal F_t$, and write $p=\alpha+\lambda+r$. $W^{(p)}$ and $Z^{(p)}(x)=1+p\int_{-\infty}^xW^{(p)}(y)\,dy$ are the scale functions of $(X,\mathbb P)$. Let $\kappa_*=\inf\{x\ge0: Z^{(p)}(x)-pW^{(p)}(x)\le-\lambda/(p-\lambda)\}$, let $h(z)=(p-\lambda)e^zZ^{(p)}(\kappa_*-z)/p+\lambda e^z/p$, and write $W^{(p)}(0+)$ for the right limit of $W^{(p)}$ at $0$. Then:
--
--   1. If $W^{(p)}(0+)\ge(p-\lambda)^{-1}$, then $\kappa_*=0$.
--   2. If $W^{(p)}(0+)<(p-\lambda)^{-1}$, then $\kappa_*>0$ is the unique root in $[0,\infty)$ of
--   $$
--   Z^{(p)}(x)-pW^{(p)}(x)=-\frac{\lambda}{p-\lambda},
--   $$
--   and for every starting state with $s-x\ge0$ (under $\mathbb P^1_{s,x}$, $Y_0=s-x$) the process
--   $$
--   e^{-(\alpha+\lambda)(\tau_{\kappa_*}\wedge t)}h\big(Y_{\tau_{\kappa_*}\wedge t}\big)+\lambda\int_0^{\tau_{\kappa_*}\wedge t}e^{-(\alpha+\lambda)u+Y_u}\,du,\qquad t\ge0,
--   $$
--   is a $\mathbb P^1_{s,x}$-martingale with respect to $\mathbf F$.
--
--   This is the martingale half of the verification argument for Theorem 3: stopping at $\tau_{\kappa_*}$ realizes the candidate value $h$.
--
--   **Formalization Note (corrected misprints)** As printed on p. 234, the thresholds are "$W^{(p)}(0^+)\ge p^{-1}$" and "$Z^{(p)}(x)-pW^{(p)}(x)=-\lambda/p$". Both are misprints: the definition of $\kappa_*$ (p. 233) uses $-\lambda/(p-\lambda)$, $\kappa_*=0$ holds exactly when $1-pW^{(p)}(0+)\le-\lambda/(p-\lambda)$, i.e. $W^{(p)}(0+)\ge(p-\lambda)^{-1}$, and the proof of Theorem 3 (p. 235) uses $(p-\lambda)^{-1}$. As printed, the first claim would be false when $p^{-1}\le W^{(p)}(0+)<(p-\lambda)^{-1}$. We state the corrected lemma. "The unique root" is uniqueness on $[0,\infty)$, the domain of $f$ in Lemma 2. $\tau_{\kappa_*}\wedge t$ equals $t$ on $\{\tau_{\kappa_*}=\infty\}$. The martingale property includes integrability and adaptedness (Mathlib's `Martingale`).
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 234, Lemma 4 (with the misprints p^{−1} → (p − λ)^{−1} and −λ/p → −λ/(p − λ) corrected per p. 233 and p. 235)

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

/-- Lemma 4, p. 234, **with its two misprints corrected** (the page has `p⁻¹` for `(p - λ)⁻¹` and
`-λ/p` for `-λ/(p - λ)`; see the definition of `κ_*` on p. 233 and the proof of Theorem 3 on p. 235).
With `p = α + λ + r`, `κ_*` as in Theorem 3 and `W^{(p)}(0+)` the right limit at `0`:
1. if `W^{(p)}(0+) ≥ (p - λ)⁻¹` then `κ_* = 0`;
2. if `W^{(p)}(0+) < (p - λ)⁻¹` then `κ_* > 0` is the unique root on `[0, ∞)` of
   `Z^{(p)}(x) - pW^{(p)}(x) = -λ/(p - λ)`, and for every starting state with `s - x ≥ 0` the stopped
   process `U_{τ_{κ_*} ∧ t} = e^{-(α+λ)(τ_{κ_*}∧t)} h(Y_{τ_{κ_*}∧t}) + λ ∫_0^{τ_{κ_*}∧t} e^{-(α+λ)u+Y_u} du`,
   `t ≥ 0`, is a `ℙ^1_{s,x}`-martingale (`Q`, `𝓕`, `Y = refl s x X`). -/
theorem lemma4_kappa_martingale {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (α : ℝ) (hα : 0 < α) (η : Ω → ℝ) (lam : ℝ)
    (hη : IsExpClock 𝓕 Q η lam) (p : ℝ) (hp : p = α + lam + r) :
    (1 / (p - lam) ≤ Function.rightLim (Shared.W P X 0 p) 0 → kappaLow P X p lam = 0) ∧
      (Function.rightLim (Shared.W P X 0 p) 0 < 1 / (p - lam) →
        (0 < kappaLow P X p lam ∧
          Shared.Z P X 0 p (kappaLow P X p lam) - p * Shared.W P X 0 p (kappaLow P X p lam) = -lam / (p - lam) ∧
          ∀ y : ℝ, 0 ≤ y → Shared.Z P X 0 p y - p * Shared.W P X 0 p y = -lam / (p - lam) →
            y = kappaLow P X p lam) ∧
        ∀ s x : ℝ, x ≤ s →
          Martingale
            (fun (t : ℝ≥0) ω =>
              U P X α lam p s x (Shared.stopAt t (Shared.tau s x X (kappaLow P X p lam) ω)) ω)
            𝓕 Q) := by sorry

end Avram2004.Canadized
