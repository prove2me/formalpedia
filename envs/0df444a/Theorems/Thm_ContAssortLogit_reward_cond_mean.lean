-- Prove2me | Theorems.Thm_ContAssortLogit_reward_cond_mean
-- name    : ContAssortLogit.reward_cond_mean
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:51.367977+00:00
-- url     : https://prove2.me/theorems/a4cd5182-e6ca-4efb-a717-3637320d9ea7
-- title:
--   §4.3, p.12 — the observed revenue $R_t$ has conditional mean $h(\varrho_t)$
-- statement:
--   Let $w$ be a revenue function, $v\in\mathcal V(\underline v,\overline v,D)$, $\alpha>0$, $\beta\ge0$, $\varrho_1\in[0,1]$, and let $X_1,\dots,X_T$ be a horizon-$T$ SAP$(\alpha,\beta)$ purchase process. Then for every $t\le T$ and every event $E$ of the history $X_1,\dots,X_{t-1}$,
--   $$\mathbb E\big[R_t\,\mathbf 1_E\big]=\mathbb E\big[h(\varrho_t)\,\mathbf 1_E\big],\qquad R_t=w(X_t)\,\mathbf 1\{X_t\in[w^{-1}(\varrho_t),1]\},$$
--   that is, $\mathbb E[R_t\mid X_1,\dots,X_{t-1}]=h(\varrho_t)$.
--
--   The observed revenue is an unbiased noisy observation of $h$ at the current iterate, which is what makes SAP a Robbins–Monro scheme.
--
--   Differences from the source:
--   - encoding: $w$ and $v$ are functions on $[0,1]$ → $w,v:\mathbb R\to\mathbb R$ with every hypothesis stated on $[0,1]$ (or $(0,1)$); reason: values outside $[0,1]$ never enter any quantity; same instances
--   - reading: the class $\mathcal V$ of Assumption 1, with $\sup_{y\in(0,1),v\in\mathcal V}|v'(y)|<\infty$ → the class $\mathcal V(\underline v,\overline v,D)$ with a fixed derivative bound $D$, for every $D$; reason: the supremum over all functions satisfying (i) and differentiability is $+\infty$, so the class must carry a bound $D$; every $D$ is allowed
--   - reading: $w^{-1}(\varrho)=\min\{x\in[0,1]:w(x)\ge\varrho\}$, an empty set for $\varrho>w(1)$ → $w^{-1}(\varrho)=1$ for $\varrho>w(1)$; reason: the minimum is undefined there, and $\varrho_1>w(1)$ is allowed; $1$ is the continuous, monotone extension, and the offered assortment $\{1\}$ is a null set
--   - reading: conditionally on $S_t=S$, the purchase $X_t$ is distributed as $X^S$ → conditionally on the whole history $X_1,\dots,X_{t-1}$, $X_t$ has the law of $X^{S_t}$; reason: the expectation $\mathbb E_\pi$ in (3) depends on the policy only under this reading; for SAP, $S_t$ is a function of the history
--   - encoding: purchases in $\mathcal X=[0,1]\cup\{\emptyset\}$ → purchases in $\mathbb R\oplus\{\ast\}$ (`ℝ ⊕ Unit`), the choice law putting no mass outside $[0,1]\cup\{\emptyset\}$; reason: Mathlib's measurable space on a sum type; same laws
--   - encoding: periods $t=1,\dots,T$ → indices $n=t-1=0,\dots,T-1$ (so $\varrho_1$ is index $0$ and $a_t=\alpha/((n+1)+\beta)$); reason: Lean's natural numbers start at 0; same sequence
--   - generalization: $R_t$ has conditional expected value $h(\varrho_t)$ (given $\varrho_t$) → $\mathbb E[R_t\mathbf 1_E]=\mathbb E[h(\varrho_t)\mathbf 1_E]$ for every event $E$ of the history $X_1,\dots,X_{t-1}$; reason: $\varrho_t$ is a function of the history, so conditioning on the history implies conditioning on $\varrho_t$ by the tower property
-- source:
--   Peeters, den Boer, Mandjes, Continuous Assortment Optimization with Logit Choice Probabilities under Incomplete Information, arXiv:1807.06497v4, §4.3, p.12, "the noisy observation Rt has conditional expected value h(ϱt)" (used on p.35)

import Mathlib
import Definitions.Def_ContAssortLogit_Model
import Definitions.Def_ContAssortLogit_Policy
import Definitions.Def_ContAssortLogit_Process
open MeasureTheory Set

namespace ContAssortLogit

/-- **The observed revenue has conditional mean `h(ϱ_t)`** (Peeters, den Boer & Mandjes,
arXiv:1807.06497v4, §4.3, p.12, "the noisy observation `R_t` has conditional expected value
`h(ϱ_t)`", used on p.35). For a horizon-`T` SAP process, `n < T`, and every event `E` of the
history `X 0, …, X (n − 1)`: `E[R_n 1_E] = E[h(ϱ_n) 1_E]`.

**Formalization Note.** Index `n` is the paper's period `n + 1`. Conditioning is on the whole
history, which contains `σ(ϱ_n)`. -/
theorem reward_cond_mean (w v : ℝ → ℝ) (vlo vhi D : ℝ) (hw : IsRevenueFn w)
    (hpar : ClassParams w vlo vhi) (hv : InClass vlo vhi D v) (α β ϱ₁ : ℝ) (hα : 0 < α)
    (hβ : 0 ≤ β) (hϱ₁ : ϱ₁ ∈ Icc (0 : ℝ) 1) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → PurchaseSpace) (T : ℕ) (hX : IsSAPProcess w v α β ϱ₁ T P X) (n : ℕ)
    (hn : n < T) (E : Set Ω)
    (hE : MeasurableSet[MeasurableSpace.comap (fun ω (i : Fin n) => X i ω) inferInstance] E) :
    ∫ ω in E, sapReward w (sapRho w α β ϱ₁ (fun i => X i ω) n) (X n ω) ∂P =
      ∫ ω in E, hfun w v (sapRho w α β ϱ₁ (fun i => X i ω) n) ∂P := by sorry

end ContAssortLogit
