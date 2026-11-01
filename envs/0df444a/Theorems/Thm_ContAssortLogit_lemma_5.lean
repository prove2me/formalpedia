-- Prove2me | Theorems.Thm_ContAssortLogit_lemma_5
-- name    : ContAssortLogit.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:56.945628+00:00
-- url     : https://prove2.me/theorems/fb7b403f-828c-49bc-a0c4-59069223e61f
-- title:
--   Lemma 5, p.36 — $\delta_t\le\kappa/(t+\beta)$
-- statement:
--   Let $w$ be a revenue function, $\overline v>\underline v>0$ class parameters with derivative bound $D$, and SAP$(\alpha,\beta)$ with $\alpha\ge\overline v+1$, $\beta\ge\max\{0,\alpha-1\}$, $\varrho_1\in[0,1]$. There exists $\kappa>0$ such that for every $v\in\mathcal V(\underline v,\overline v,D)$, every SAP purchase process and all $t\in\mathbb N$,
--   $$\delta_t\le\frac{\kappa}{t+\beta}.\tag{26}$$
--
--   The mean squared error of the SAP iterate decays at the rate $1/t$, uniformly over the class.
--
--   Differences from the source:
--   - encoding: $w$ and $v$ are functions on $[0,1]$ → $w,v:\mathbb R\to\mathbb R$ with every hypothesis stated on $[0,1]$ (or $(0,1)$); reason: values outside $[0,1]$ never enter any quantity; same instances
--   - reading: the class $\mathcal V$ of Assumption 1, with $\sup_{y\in(0,1),v\in\mathcal V}|v'(y)|<\infty$ → the class $\mathcal V(\underline v,\overline v,D)$ with a fixed derivative bound $D$, for every $D$; reason: the supremum over all functions satisfying (i) and differentiability is $+\infty$, so the class must carry a bound $D$; every $D$ is allowed
--   - reading: $w^{-1}(\varrho)=\min\{x\in[0,1]:w(x)\ge\varrho\}$, an empty set for $\varrho>w(1)$ → $w^{-1}(\varrho)=1$ for $\varrho>w(1)$; reason: the minimum is undefined there, and $\varrho_1>w(1)$ is allowed; $1$ is the continuous, monotone extension, and the offered assortment $\{1\}$ is a null set
--   - reading: conditionally on $S_t=S$, the purchase $X_t$ is distributed as $X^S$ → conditionally on the whole history $X_1,\dots,X_{t-1}$, $X_t$ has the law of $X^{S_t}$; reason: the expectation $\mathbb E_\pi$ in (3) depends on the policy only under this reading; for SAP, $S_t$ is a function of the history
--   - encoding: purchases in $\mathcal X=[0,1]\cup\{\emptyset\}$ → purchases in $\mathbb R\oplus\{\ast\}$ (`ℝ ⊕ Unit`), the choice law putting no mass outside $[0,1]\cup\{\emptyset\}$; reason: Mathlib's measurable space on a sum type; same laws
--   - encoding: $\mathcal S=\{S\in\mathcal B[0,1]:\mathrm{vol}(S)\le c\}$ with $c=1$, and $\varrho^*=\max\{r(S,v):S\in\mathcal S\}$ → $\mathcal S$ = measurable subsets of $[0,1]$, and $\varrho^*$ = the supremum of $r(\cdot,v)$ over $\mathcal S$; reason: the volume constraint is void for $c=1$; the supremum is attained (§4.1), so it is the maximum
--   - encoding: periods $t=1,\dots,T$ → indices $n=t-1=0,\dots,T-1$ (so $\varrho_1$ is index $0$ and $a_t=\alpha/((n+1)+\beta)$); reason: Lean's natural numbers start at 0; same sequence
--   - encoding: for any $t\in\mathbb N$ → for every horizon $T$ and every index the horizon-$T$ process determines; reason: the process of §3 is defined for a horizon $T$; $T$ is arbitrary, so all $t$ are covered
--   - generalization: there exists a $\kappa>0$ such that $\delta_t\le\kappa/(t+\beta)$ for all $t$ (for the given $v$) → $\kappa$ chosen after $w,\underline v,\overline v,D,\alpha,\beta,\varrho_1$ and before the horizon, $v\in\mathcal V$ and the process; reason: a uniform $\kappa$ gives the per-$v$ statement; the paper's $\kappa=\max\{1+\beta,\alpha(1+\overline v)\}$ is uniform, and Theorem 1's worst-case bound needs it
-- source:
--   Peeters, den Boer, Mandjes, Continuous Assortment Optimization with Logit Choice Probabilities under Incomplete Information, arXiv:1807.06497v4, Lemma 5, (26), p.36

import Mathlib
import Definitions.Def_ContAssortLogit_Model
import Definitions.Def_ContAssortLogit_Policy
import Definitions.Def_ContAssortLogit_Process
open MeasureTheory Set

namespace ContAssortLogit

universe u

/-- **Lemma 5** (Peeters, den Boer & Mandjes, arXiv:1807.06497v4, App. A.1, p.36): there exists
`κ > 0` such that `δ_t ≤ κ / (t + β)` for all `t ∈ ℕ`, where `δ_t = E_π[(ϱ_t − ϱ*)²]` for
SAP(α, β) with `α ≥ v̄ + 1`, `β ≥ max{0, α − 1}`.

**Formalization Note.** `κ` is chosen after `w`, the class parameters and the policy parameters, and
before the horizon, `v ∈ 𝒱` and the process (uniform over the class, as the paper's
`κ = max{1 + β, α(1 + v̄)}` is). 0-based time: `sapMSE … n` is `δ_{n+1}`; a horizon-`T` process
determines `δ_1, …, δ_{T+1}`, i.e. `n ≤ T`. -/
theorem lemma_5 (w : ℝ → ℝ) (vlo vhi D : ℝ) (hw : IsRevenueFn w)
    (hpar : ClassParams w vlo vhi) (α β ϱ₁ : ℝ) (hα : vhi + 1 ≤ α)
    (hβ : max 0 (α - 1) ≤ β) (hϱ₁ : ϱ₁ ∈ Icc (0 : ℝ) 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (T : ℕ) (v : ℝ → ℝ), InClass vlo vhi D v →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → PurchaseSpace),
        IsSAPProcess w v α β ϱ₁ T P X →
          ∀ n ≤ T, sapMSE w v α β ϱ₁ P X n ≤ κ / ((n + 1 : ℝ) + β) := by sorry

end ContAssortLogit
