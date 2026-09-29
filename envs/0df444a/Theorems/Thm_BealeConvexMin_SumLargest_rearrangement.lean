-- Prove2me | Theorems.Thm_BealeConvexMin_SumLargest_rearrangement
-- name    : BealeConvexMin.SumLargest.rearrangement
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:39:22.523975+00:00
-- url     : https://prove2.me/theorems/659973a3-836e-4417-817a-110edb508d10
-- title:
--   Proof of Theorem 1 (a), p. 180 — $C$ rewritten when $u'_1\le\dots\le u'_s$ and $u'_\tau\le0$
-- statement:
--   In the setting of Theorem 1 (a) of Beale's paper, let $1\le\tau\le s$, let $z'$ be any values of the $z$ variables, and let $u'_1\le u'_2\le\dots\le u'_s$ with $u'_\tau\le0$ (so that $L_1,\dots,L_\tau$ are all at least $L_0$). Write $w_f=\varphi_f+\tau\theta_f$. Then
--   $$C=A_0+\tau c_{00}+\sum_l(A_l+\tau c_{0l})z'_l+\sum_{f=1}^{\tau}(w_f-1)u'_f+\sum_{f=\tau+1}^{s}w_f u'_f$$
--   $$\phantom{C}=A_0+\tau c_{00}+\sum_l(A_l+\tau c_{0l})z'_l+\sum_{f=1}^{\tau}(w_f-1)(u'_f-u'_\tau)+\sum_{f=\tau+1}^{s}w_f(u'_f-u'_\tau)+\Bigl\{\sum_{f=1}^{s}w_f-\tau\Bigr\}u'_\tau ,$$
--   where $C$ is evaluated at $(z',u')$.
--
--   This identity is the core of Beale's proof of the sufficiency direction of Theorem 1 (a): under the ordering, each bracketed coefficient multiplies a quantity of known sign, and (4.5) makes every term non-negative.
--
--   **Formalization Note** The paper's $f=1,\dots,s$ are Lean's $0,\dots,s-1$, so "$f\le\tau$" is `(f : ℕ) < τ`, "$f>\tau$" is `τ ≤ (f : ℕ)`, and $u'_\tau$ is `u' ⟨τ - 1, _⟩`. The hypothesis $\tau\ge1$ is added: at $\tau=0$ the paper's $u'_\tau$ does not exist. The page's second line prints $(A_l+\tau c_l)$; this is a misprint for $(A_l+\tau c_{0l})$, which is what the first line and the rest of the proof use, and $c_{0l}$ is stated. The identity holds for every $z'$, whether or not the restricted $z'_l$ are non-negative.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 180 (PDF p. 8), proof of Theorem 1 (a), the display after "Then"

import Mathlib
import Definitions.Def_BealeConvexMin_SumLargest_sumLargest
import Definitions.Def_BealeConvexMin_SumLargest_Forms

namespace BealeConvexMin.SumLargest

/-- Beale (1955), proof of Theorem 1 (a), p. 180, the display after "Then". If
`u'_1 ≤ u'_2 ≤ ⋯ ≤ u'_s` and `u'_τ ≤ 0` (so at least `τ` of `L_1, …, L_s` are not less than
`L_0`), then

`C = A_0 + τ c_00 + Σ_l (A_l + τ c_0l) z'_l + Σ_{f=1}^{τ} (φ_f + τθ_f − 1) u'_f
      + Σ_{f=τ+1}^{s} (φ_f + τθ_f) u'_f`
`  = A_0 + τ c_00 + Σ_l (A_l + τ c_0l) z'_l + Σ_{f=1}^{τ} (φ_f + τθ_f − 1)(u'_f − u'_τ)
      + Σ_{f=τ+1}^{s} (φ_f + τθ_f)(u'_f − u'_τ) + {Σ_{f=1}^{s} (φ_f + τθ_f) − τ} u'_τ`.

Index shift: the paper's `f = 1, …, s` is Lean's `f = 0, …, s-1`, so the paper's `f ≤ τ` is
`(f : ℕ) < τ`, `f > τ` is `τ ≤ (f : ℕ)`, and `u'_τ` is `u' ⟨τ - 1, _⟩`. The page's second line
prints `c_l` for `c_0l` (a misprint); `c_0l` is used here. -/
theorem rearrangement {r s : ℕ} (P : Forms r s) (τ : ℕ) (hτ1 : 1 ≤ τ) (hτs : τ ≤ s)
    (z' : Fin r → ℝ) (u' : Fin s → ℝ) (hmono : Monotone u')
    (hτneg : u' ⟨τ - 1, by omega⟩ ≤ 0) :
    P.C τ z' u' =
        P.A0 + (τ : ℝ) * P.c00 + ∑ l, (P.A l + (τ : ℝ) * P.c0 l) * z' l
          + ∑ f ∈ Finset.univ.filter (fun f : Fin s => (f : ℕ) < τ),
              (P.φ f + (τ : ℝ) * P.θ f - 1) * u' f
          + ∑ f ∈ Finset.univ.filter (fun f : Fin s => τ ≤ (f : ℕ)),
              (P.φ f + (τ : ℝ) * P.θ f) * u' f ∧
    P.C τ z' u' =
        P.A0 + (τ : ℝ) * P.c00 + ∑ l, (P.A l + (τ : ℝ) * P.c0 l) * z' l
          + ∑ f ∈ Finset.univ.filter (fun f : Fin s => (f : ℕ) < τ),
              (P.φ f + (τ : ℝ) * P.θ f - 1) * (u' f - u' ⟨τ - 1, by omega⟩)
          + ∑ f ∈ Finset.univ.filter (fun f : Fin s => τ ≤ (f : ℕ)),
              (P.φ f + (τ : ℝ) * P.θ f) * (u' f - u' ⟨τ - 1, by omega⟩)
          + (∑ f, (P.φ f + (τ : ℝ) * P.θ f) - (τ : ℝ)) * u' ⟨τ - 1, by omega⟩ := by sorry

end BealeConvexMin.SumLargest
