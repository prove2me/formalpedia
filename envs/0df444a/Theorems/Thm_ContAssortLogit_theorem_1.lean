-- Prove2me | Theorems.Thm_ContAssortLogit_theorem_1
-- name    : ContAssortLogit.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:43.356188+00:00
-- url     : https://prove2.me/theorems/e3e7e014-823e-45ec-a2b1-7b38520d7583
-- title:
--   Theorem 1, p.12 — SAP$(\alpha,\beta)$ has worst-case regret $O(\log T)$
-- statement:
--   Let $w:[0,1]\to[0,1]$ be continuously differentiable with derivative bounded below by a positive constant. Let $\overline v>\underline v>0$ with $\overline v>w(0)/\int_0^1(w(x)-w(0))\,dx$, let $D$ be a derivative bound, and let $\mathcal V=\mathcal V(\underline v,\overline v,D)$ be the class of preference functions $v$ with $\underline v\le v\le\overline v$ on $[0,1]$, integrable on $[0,1]$, and differentiable on $(0,1)$ with $|v'|\le D$ there (Assumption 1).
--
--   Let $\pi$ correspond to SAP$(\alpha,\beta)$ with
--   $$\alpha\ge\overline v+1,\qquad\beta\ge\max\{0,\alpha-1\},$$
--   and initial value $\varrho_1\in[0,1]$. Then there is a $\overline C>0$ such that, for all $T\ge2$,
--   $$\Delta_\pi(T)=\sup_{v\in\mathcal V}\Delta_\pi(T,v)\le\overline C\log T,$$
--   where $\Delta_\pi(T,v)=\sum_{t=1}^T\mathbb E_\pi[\max_{S\in\mathcal S}r(S,v)-r(S_t,v)]$ is the regret of SAP when customers choose according to the continuous logit law with preference function $v$.
--
--   A simple stochastic approximation policy, which never estimates $v$, learns the optimal assortment with regret growing only logarithmically in the horizon, uniformly over the class of preference functions; Theorem 2 of the paper shows this rate cannot be improved.
--
--   Differences from the source:
--   - encoding: $w$ and $v$ are functions on $[0,1]$ → $w,v:\mathbb R\to\mathbb R$ with every hypothesis stated on $[0,1]$ (or $(0,1)$); reason: values outside $[0,1]$ never enter any quantity; same instances
--   - reading: the class $\mathcal V$ of Assumption 1, with $\sup_{y\in(0,1),v\in\mathcal V}|v'(y)|<\infty$ → the class $\mathcal V(\underline v,\overline v,D)$ with a fixed derivative bound $D$, for every $D$; reason: the supremum over all functions satisfying (i) and differentiability is $+\infty$, so the class must carry a bound $D$; every $D$ is allowed
--   - reading: $w^{-1}(\varrho)=\min\{x\in[0,1]:w(x)\ge\varrho\}$, an empty set for $\varrho>w(1)$ → $w^{-1}(\varrho)=1$ for $\varrho>w(1)$; reason: the minimum is undefined there, and $\varrho_1>w(1)$ is allowed; $1$ is the continuous, monotone extension, and the offered assortment $\{1\}$ is a null set
--   - reading: conditionally on $S_t=S$, the purchase $X_t$ is distributed as $X^S$ → conditionally on the whole history $X_1,\dots,X_{t-1}$, $X_t$ has the law of $X^{S_t}$; reason: the expectation $\mathbb E_\pi$ in (3) depends on the policy only under this reading; for SAP, $S_t$ is a function of the history
--   - reading: there is a $\overline C>0$ (independent of $v\in\mathcal V$, Remark 4) → $\overline C$ is chosen after $w$, $\underline v,\overline v,D$, $\alpha,\beta,\varrho_1$ and before $T$, $v$ and the probability space; reason: Theorem 1 is a worst-case bound (Remark 4); the constant may depend on the policy parameters (Remark 3)
--   - encoding: purchases in $\mathcal X=[0,1]\cup\{\emptyset\}$ → purchases in $\mathbb R\oplus\{\ast\}$ (`ℝ ⊕ Unit`), the choice law putting no mass outside $[0,1]\cup\{\emptyset\}$; reason: Mathlib's measurable space on a sum type; same laws
--   - encoding: $\mathcal S=\{S\in\mathcal B[0,1]:\mathrm{vol}(S)\le c\}$ with $c=1$, and $\varrho^*=\max\{r(S,v):S\in\mathcal S\}$ → $\mathcal S$ = measurable subsets of $[0,1]$, and $\varrho^*$ = the supremum of $r(\cdot,v)$ over $\mathcal S$; reason: the volume constraint is void for $c=1$; the supremum is attained (§4.1), so it is the maximum
--   - encoding: periods $t=1,\dots,T$ → indices $n=t-1=0,\dots,T-1$ (so $\varrho_1$ is index $0$ and $a_t=\alpha/((n+1)+\beta)$); reason: Lean's natural numbers start at 0; same sequence
--   - encoding: $\Delta_\pi(T)=\sup_{v\in\mathcal V}\Delta_\pi(T,v)\le\overline C\log T$ → $\Delta_\pi(T,v)\le\overline C\log T$ for every $v\in\mathcal V$ and every probability space carrying the process; reason: a supremum is bounded by $\overline C\log T$ iff every member is
-- source:
--   Peeters, den Boer, Mandjes, Continuous Assortment Optimization with Logit Choice Probabilities under Incomplete Information, arXiv:1807.06497v4, Theorem 1, p.12

import Mathlib
import Definitions.Def_ContAssortLogit_Model
import Definitions.Def_ContAssortLogit_Policy
import Definitions.Def_ContAssortLogit_Process
open MeasureTheory Set

namespace ContAssortLogit

universe u

/-- **Theorem 1** (Peeters, den Boer & Mandjes, arXiv:1807.06497v4, §4.3, p.12). Let `π` correspond
to SAP(α, β) with `α ≥ v̄ + 1` and `β ≥ max{0, α − 1}`. Then there is a `C̄ > 0` such that, for all
`T ≥ 2`, `Δ_π(T) ≤ C̄ log T`, where `Δ_π(T) = sup_{v ∈ 𝒱} Δ_π(T, v)` is the worst-case regret over
the class `𝒱` of Assumption 1.

**Formalization Note.** `C̄` is chosen after the revenue function `w`, the class parameters
`v̲, v̄, D` and the policy parameters `α, β, ϱ₁`, and before the horizon `T`, the preference
function `v ∈ 𝒱` and the probability space; the worst case `sup_{v ∈ 𝒱}` is the `∀ v`. The
purchases are a horizon-`T` SAP process (`IsSAPProcess`): conditionally on the history, the
purchase in period `t` has the choice law (1) of the offered assortment `[w⁻¹(ϱ_t), 1]`. -/
theorem theorem_1 (w : ℝ → ℝ) (vlo vhi D : ℝ) (hw : IsRevenueFn w)
    (hpar : ClassParams w vlo vhi) (α β ϱ₁ : ℝ) (hα : vhi + 1 ≤ α)
    (hβ : max 0 (α - 1) ≤ β) (hϱ₁ : ϱ₁ ∈ Icc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 2 ≤ T → ∀ v : ℝ → ℝ, InClass vlo vhi D v →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → PurchaseSpace),
        IsSAPProcess w v α β ϱ₁ T P X → regret w v α β ϱ₁ T P X ≤ C * Real.log T := by sorry

end ContAssortLogit
