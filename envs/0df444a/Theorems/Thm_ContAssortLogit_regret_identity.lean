-- Prove2me | Theorems.Thm_ContAssortLogit_regret_identity
-- name    : ContAssortLogit.regret_identity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:48.506733+00:00
-- url     : https://prove2.me/theorems/d5858819-966c-4489-a2a2-1b5489000afb
-- title:
--   App. A.1, p.36 — $\Delta_\pi(T,v)=\sum_{t=1}^T\mathbb E_\pi[h(\varrho^*)-h(\varrho_t)]$
-- statement:
--   Let $w$ be a revenue function, $v\in\mathcal V(\underline v,\overline v,D)$, and let $X_1,\dots,X_T$ be a horizon-$T$ purchase process of SAP$(\alpha,\beta)$ with $\alpha>0$, $\beta\ge0$, $\varrho_1\in[0,1]$. Then the regret equals
--   $$\Delta_\pi(T,v)=\sum_{t=1}^T\mathbb E_\pi\big[h(\varrho^*)-h(\varrho_t)\big].$$
--
--   This rewrites the regret in terms of the map $h$, so that the quadratic gap (24) and the rate of Lemma 5 apply.
--
--   Differences from the source:
--   - encoding: $w$ and $v$ are functions on $[0,1]$ → $w,v:\mathbb R\to\mathbb R$ with every hypothesis stated on $[0,1]$ (or $(0,1)$); reason: values outside $[0,1]$ never enter any quantity; same instances
--   - reading: the class $\mathcal V$ of Assumption 1, with $\sup_{y\in(0,1),v\in\mathcal V}|v'(y)|<\infty$ → the class $\mathcal V(\underline v,\overline v,D)$ with a fixed derivative bound $D$, for every $D$; reason: the supremum over all functions satisfying (i) and differentiability is $+\infty$, so the class must carry a bound $D$; every $D$ is allowed
--   - reading: $w^{-1}(\varrho)=\min\{x\in[0,1]:w(x)\ge\varrho\}$, an empty set for $\varrho>w(1)$ → $w^{-1}(\varrho)=1$ for $\varrho>w(1)$; reason: the minimum is undefined there, and $\varrho_1>w(1)$ is allowed; $1$ is the continuous, monotone extension, and the offered assortment $\{1\}$ is a null set
--   - reading: conditionally on $S_t=S$, the purchase $X_t$ is distributed as $X^S$ → conditionally on the whole history $X_1,\dots,X_{t-1}$, $X_t$ has the law of $X^{S_t}$; reason: the expectation $\mathbb E_\pi$ in (3) depends on the policy only under this reading; for SAP, $S_t$ is a function of the history
--   - encoding: purchases in $\mathcal X=[0,1]\cup\{\emptyset\}$ → purchases in $\mathbb R\oplus\{\ast\}$ (`ℝ ⊕ Unit`), the choice law putting no mass outside $[0,1]\cup\{\emptyset\}$; reason: Mathlib's measurable space on a sum type; same laws
--   - encoding: $\mathcal S=\{S\in\mathcal B[0,1]:\mathrm{vol}(S)\le c\}$ with $c=1$, and $\varrho^*=\max\{r(S,v):S\in\mathcal S\}$ → $\mathcal S$ = measurable subsets of $[0,1]$, and $\varrho^*$ = the supremum of $r(\cdot,v)$ over $\mathcal S$; reason: the volume constraint is void for $c=1$; the supremum is attained (§4.1), so it is the maximum
--   - encoding: periods $t=1,\dots,T$ → indices $n=t-1=0,\dots,T-1$ (so $\varrho_1$ is index $0$ and $a_t=\alpha/((n+1)+\beta)$); reason: Lean's natural numbers start at 0; same sequence
--   - generalization: SAP$(\alpha,\beta)$ with $\alpha\ge\overline v+1$, $\beta\ge\max\{0,\alpha-1\}$ (the hypotheses of Theorem 1, in whose proof the identity appears) → any $\alpha>0$, $\beta\ge0$ (the range of §4.2); reason: the identity uses only $h(\varrho^*)=\varrho^*$ and $h(\varrho_t)=r(S_t,v)$, which hold for every parameter choice; Theorem 1's parameters are a special case
-- source:
--   Peeters, den Boer, Mandjes, Continuous Assortment Optimization with Logit Choice Probabilities under Incomplete Information, arXiv:1807.06497v4, App. A.1, p.36, first equality of the regret display

import Mathlib
import Definitions.Def_ContAssortLogit_Model
import Definitions.Def_ContAssortLogit_Policy
import Definitions.Def_ContAssortLogit_Process
open MeasureTheory Set

namespace ContAssortLogit

/-- **The regret as a sum of `h`-gaps** (Peeters, den Boer & Mandjes, arXiv:1807.06497v4,
App. A.1, p.36): `Δ_π(T, v) = Σ_{t=1}^T E_π[h(ϱ*) − h(ϱ_t)]` for the policy `π = SAP(α, β)`.

**Formalization Note.** 0-based time: the sum runs over `n = 0, …, T − 1`. -/
theorem regret_identity (w v : ℝ → ℝ) (vlo vhi D : ℝ) (hw : IsRevenueFn w)
    (hpar : ClassParams w vlo vhi) (hv : InClass vlo vhi D v) (α β ϱ₁ : ℝ) (hα : 0 < α)
    (hβ : 0 ≤ β) (hϱ₁ : ϱ₁ ∈ Icc (0 : ℝ) 1) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → PurchaseSpace) (T : ℕ) (hX : IsSAPProcess w v α β ϱ₁ T P X) :
    regret w v α β ϱ₁ T P X =
      ∑ n ∈ Finset.range T,
        ∫ ω, (hfun w v (optRev w v) - hfun w v (sapRho w α β ϱ₁ (fun i => X i ω) n)) ∂P := by sorry

end ContAssortLogit
