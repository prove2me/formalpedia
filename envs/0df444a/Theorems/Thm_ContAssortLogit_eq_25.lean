-- Prove2me | Theorems.Thm_ContAssortLogit_eq_25
-- name    : ContAssortLogit.eq_25
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:37:00.280297+00:00
-- url     : https://prove2.me/theorems/f404b43b-ee13-4f33-8746-d10886a5c190
-- title:
--   (25), p.36 — $\delta_{t+1}\le\delta_t\big(1-\frac{2}{1+\overline v}\frac{\alpha}{t+\beta}\big)+\frac{\alpha^2}{(t+\beta)^2}$
-- statement:
--   Let $w$ be a revenue function, $v\in\mathcal V(\underline v,\overline v,D)$, and let SAP$(\alpha,\beta)$ have $\alpha\ge\overline v+1$, $\beta\ge\max\{0,\alpha-1\}$ and $\varrho_1\in[0,1]$. For a horizon-$T$ SAP purchase process let $\delta_t=\mathbb E_\pi[(\varrho_t-\varrho^*)^2]$. Then for every $t=1,\dots,T$,
--   $$\delta_{t+1}\le\delta_t\Big(1-\frac{2}{1+\overline v}\cdot\frac{\alpha}{t+\beta}\Big)+\frac{\alpha^2}{(t+\beta)^2}.\tag{25}$$
--
--   This is the one-step contraction of the mean squared error from which Lemma 5 follows by induction.
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
-- source:
--   Peeters, den Boer, Mandjes, Continuous Assortment Optimization with Logit Choice Probabilities under Incomplete Information, arXiv:1807.06497v4, App. A.1, (25), p.36

import Mathlib
import Definitions.Def_ContAssortLogit_Model
import Definitions.Def_ContAssortLogit_Policy
import Definitions.Def_ContAssortLogit_Process
open MeasureTheory Set

namespace ContAssortLogit

/-- **Inequality (25)** (Peeters, den Boer & Mandjes, arXiv:1807.06497v4, App. A.1, p.36): with
`δ_t = E_π[(ϱ_t − ϱ*)²]`,
`δ_{t+1} ≤ δ_t (1 − (2 / (1 + v̄)) · α / (t + β)) + α² / (t + β)²`,
for SAP(α, β) with `α ≥ v̄ + 1`, `β ≥ max{0, α − 1}`.

**Formalization Note.** 0-based time: `sapMSE … n` is `δ_{n+1}`, so the paper's `t` is `n + 1`.
For a horizon-`T` process the inequality is stated for `n < T`, i.e. for `t = 1, …, T`. -/
theorem eq_25 (w v : ℝ → ℝ) (vlo vhi D : ℝ) (hw : IsRevenueFn w)
    (hpar : ClassParams w vlo vhi) (hv : InClass vlo vhi D v) (α β ϱ₁ : ℝ) (hα : vhi + 1 ≤ α)
    (hβ : max 0 (α - 1) ≤ β) (hϱ₁ : ϱ₁ ∈ Icc (0 : ℝ) 1) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → PurchaseSpace) (T : ℕ) (hX : IsSAPProcess w v α β ϱ₁ T P X)
    (n : ℕ) (hn : n < T) :
    sapMSE w v α β ϱ₁ P X (n + 1) ≤
      sapMSE w v α β ϱ₁ P X n * (1 - 2 / (1 + vhi) * (α / ((n + 1 : ℝ) + β))) +
        α ^ 2 / ((n + 1 : ℝ) + β) ^ 2 := by sorry

end ContAssortLogit
