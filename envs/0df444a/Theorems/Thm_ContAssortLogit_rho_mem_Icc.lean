-- Prove2me | Theorems.Thm_ContAssortLogit_rho_mem_Icc
-- name    : ContAssortLogit.rho_mem_Icc
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:35:48.694299+00:00
-- url     : https://prove2.me/theorems/bb782ae4-d76f-450e-b5f8-da31b9dd1239
-- title:
--   App. A.1, p.35 — the SAP iterates stay in $[0,1]$
-- statement:
--   Let $w$ be a revenue function, $\alpha>0$, $\beta\ge\max\{0,\alpha-1\}$ and $\varrho_1\in[0,1]$. Then the iterates of SAP$(\alpha,\beta)$ satisfy
--   $$\varrho_t\in[0,1]\qquad\text{for all }t\in\mathbb N.$$
--
--   The choice $\beta\ge\alpha-1$ makes every step size $a_t=\alpha/(t+\beta)$ at most $1$, so each update is a convex combination of $\varrho_t$ and the observed revenue $R_t\in[0,1]$.
--
--   Differences from the source:
--   - encoding: $w$ and $v$ are functions on $[0,1]$ → $w,v:\mathbb R\to\mathbb R$ with every hypothesis stated on $[0,1]$ (or $(0,1)$); reason: values outside $[0,1]$ never enter any quantity; same instances
--   - reading: $w^{-1}(\varrho)=\min\{x\in[0,1]:w(x)\ge\varrho\}$, an empty set for $\varrho>w(1)$ → $w^{-1}(\varrho)=1$ for $\varrho>w(1)$; reason: the minimum is undefined there, and $\varrho_1>w(1)$ is allowed; $1$ is the continuous, monotone extension, and the offered assortment $\{1\}$ is a null set
--   - encoding: periods $t=1,\dots,T$ → indices $n=t-1=0,\dots,T-1$ (so $\varrho_1$ is index $0$ and $a_t=\alpha/((n+1)+\beta)$); reason: Lean's natural numbers start at 0; same sequence
--   - encoding: $\varrho_t\in[0,1]$ for the iterates of SAP$(\alpha,\beta)$ → $\varrho_t\in[0,1]$ for the SAP iterates along every sequence of (no-)purchases; reason: the iterate is a deterministic function of the purchases, so this is the same as holding on every realization
--   - generalization: SAP$(\alpha,\beta)$ with $\alpha\ge\overline v+1$ (the standing choice in the proof of Theorem 1) → any $\alpha>0$ (the range of §4.2); reason: the claim uses only $\alpha>0$ and $\beta\ge\max\{0,\alpha-1\}$; every $\alpha\ge\overline v+1$ is such an $\alpha$
-- source:
--   Peeters, den Boer, Mandjes, Continuous Assortment Optimization with Logit Choice Probabilities under Incomplete Information, arXiv:1807.06497v4, App. A.1, p.35, "by our choice of β ⩾ max{0, α − 1} it follows that ϱt ∈ [0, 1] for all t ∈ N"

import Mathlib
import Definitions.Def_ContAssortLogit_Model
import Definitions.Def_ContAssortLogit_Policy
open MeasureTheory Set

namespace ContAssortLogit

/-- **The SAP iterates stay in `[0, 1]`** (Peeters, den Boer & Mandjes, arXiv:1807.06497v4,
App. A.1, p.35): "by our choice of `β ≥ max{0, α − 1}` it follows that `ϱ_t ∈ [0, 1]` for all
`t ∈ ℕ`". This holds for every sequence of (no-)purchases.

**Formalization Note.** Index `n` is the paper's period `n + 1`. -/
theorem rho_mem_Icc (w : ℝ → ℝ) (hw : IsRevenueFn w) (α β ϱ₁ : ℝ) (hα : 0 < α)
    (hβ : max 0 (α - 1) ≤ β) (hϱ₁ : ϱ₁ ∈ Icc (0 : ℝ) 1) :
    ∀ (X : ℕ → PurchaseSpace) (n : ℕ), sapRho w α β ϱ₁ X n ∈ Icc (0 : ℝ) 1 := by sorry

end ContAssortLogit
