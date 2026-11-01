-- Prove2me | Theorems.Thm_ContAssortLogit_sap_process_exists
-- name    : ContAssortLogit.sap_process_exists
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:53.317391+00:00
-- url     : https://prove2.me/theorems/537f6ff3-7a68-4628-bd62-45ef0f6ee5a9
-- title:
--   §3, p.7 — the SAP$(\alpha,\beta)$ purchase process exists
-- statement:
--   Let $w$ be a revenue function (continuously differentiable $[0,1]\to[0,1]$ with derivative bounded below by a positive constant), let $\overline v>\underline v>0$ with $\overline v>w(0)/\int_0^1(w(x)-w(0))\,dx$, let $v\in\mathcal V(\underline v,\overline v,D)$, and let $\alpha>0$, $\beta\ge0$, $\varrho_1\in[0,1]$. Then for every horizon $T\in\mathbb N$ there is a probability space carrying (no-)purchases $X_1,\dots,X_T$ such that, for each $t$, conditionally on $X_1,\dots,X_{t-1}$,
--   $$X_t\ \text{is distributed as}\ X^{S_t},\qquad S_t=[w^{-1}(\varrho_t),1],$$
--   where $\varrho_t$ are the SAP$(\alpha,\beta)$ iterates.
--
--   This is the well-posedness of the sequential model of §3 ("Conditionally on $S_t=S$, the purchase $X_t$ is distributed as $X^S$") for the policy SAP$(\alpha,\beta)$. The paper takes it for granted; it is not a numbered result. It shows that the regret bound of Theorem 1, which quantifies over all such processes, is not vacuous.
--
--   Differences from the source:
--   - encoding: $w$ and $v$ are functions on $[0,1]$ → $w,v:\mathbb R\to\mathbb R$ with every hypothesis stated on $[0,1]$ (or $(0,1)$); reason: values outside $[0,1]$ never enter any quantity; same instances
--   - reading: the class $\mathcal V$ of Assumption 1, with $\sup_{y\in(0,1),v\in\mathcal V}|v'(y)|<\infty$ → the class $\mathcal V(\underline v,\overline v,D)$ with a fixed derivative bound $D$, for every $D$; reason: the supremum over all functions satisfying (i) and differentiability is $+\infty$, so the class must carry a bound $D$; every $D$ is allowed
--   - reading: $w^{-1}(\varrho)=\min\{x\in[0,1]:w(x)\ge\varrho\}$, an empty set for $\varrho>w(1)$ → $w^{-1}(\varrho)=1$ for $\varrho>w(1)$; reason: the minimum is undefined there, and $\varrho_1>w(1)$ is allowed; $1$ is the continuous, monotone extension, and the offered assortment $\{1\}$ is a null set
--   - reading: conditionally on $S_t=S$, the purchase $X_t$ is distributed as $X^S$ → conditionally on the whole history $X_1,\dots,X_{t-1}$, $X_t$ has the law of $X^{S_t}$; reason: the expectation $\mathbb E_\pi$ in (3) depends on the policy only under this reading; for SAP, $S_t$ is a function of the history
--   - encoding: purchases in $\mathcal X=[0,1]\cup\{\emptyset\}$ → purchases in $\mathbb R\oplus\{\ast\}$ (`ℝ ⊕ Unit`), the choice law putting no mass outside $[0,1]\cup\{\emptyset\}$; reason: Mathlib's measurable space on a sum type; same laws
--   - encoding: periods $t=1,\dots,T$ → indices $n=t-1=0,\dots,T-1$ (so $\varrho_1$ is index $0$ and $a_t=\alpha/((n+1)+\beta)$); reason: Lean's natural numbers start at 0; same sequence
-- source:
--   Peeters, den Boer, Mandjes, Continuous Assortment Optimization with Logit Choice Probabilities under Incomplete Information, arXiv:1807.06497v4, §3, p.7, "Conditionally on St = S, the purchase Xt is distributed as XS", with (2), p.8, and §4.2, p.11

import Mathlib
import Definitions.Def_ContAssortLogit_Model
import Definitions.Def_ContAssortLogit_Policy
import Definitions.Def_ContAssortLogit_Process
open MeasureTheory Set

namespace ContAssortLogit

/-- **Well-posedness of the model** (Peeters, den Boer & Mandjes, arXiv:1807.06497v4, §3, p.7,
"Conditionally on `S_t = S`, the purchase `X_t` is distributed as `X^S`", with (2), p.8, and the
policy SAP(α, β), §4.2, p.11). For every revenue function `w`, every `v` in the class `𝒱`, every
choice of the SAP parameters `α > 0`, `β ≥ 0`, `ϱ₁ ∈ [0, 1]` and every horizon `T`, there is a
probability space carrying a horizon-`T` SAP(α, β) purchase process.

This is not a numbered result of the paper; it is the (implicit) statement that the sequential
model of §3 is well defined for SAP, and it shows that the regret bound of Theorem 1 is not
vacuous.

**Formalization Note.** The process is `IsSAPProcess` (conditional law given the whole history). -/
theorem sap_process_exists (w v : ℝ → ℝ) (vlo vhi D : ℝ) (hw : IsRevenueFn w)
    (hpar : ClassParams w vlo vhi) (hv : InClass vlo vhi D v) (α β ϱ₁ : ℝ) (hα : 0 < α)
    (hβ : 0 ≤ β) (hϱ₁ : ϱ₁ ∈ Icc (0 : ℝ) 1) (T : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → PurchaseSpace),
      IsSAPProcess w v α β ϱ₁ T P X := by sorry

end ContAssortLogit
