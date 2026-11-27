-- Prove2me | Theorems.Thm_ConvexRMDP_Supplement_proposition_5_2
-- name    : ConvexRMDP.Supplement.proposition_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:57:40.077013+00:00
-- url     : https://prove2.me/theorems/3c6f2449-1fa5-5438-a57e-47ebf056fba4
-- title:
--   Proposition 5.2 — conjugate of $f(p)=\prod_{s'}x_{s'}^{\gamma p_{s'}}$: $-1$ at $0$ if $x=e$; $(\alpha/\gamma)\log(\alpha/\gamma)-\alpha/\gamma$ on the ray $\alpha\log x$ otherwise
-- statement:
--   Let $\gamma \in (0,1)$, $x \in [1,+\infty)^{\mathcal S}$ and $f(p) = \prod_{s'} x_{s'}^{\gamma p_{s'}}$ for $p \in \mathbb R^{\mathcal S}$, as in (5.4), with conjugate $f^*(y) = \sup_{p \in \mathbb R^{\mathcal S}} y^\top p - f(p)$.
--
--   1. If $x = (1, \dots, 1)$, then
--   $$
--   f^*(y) = \begin{cases} -1 & \text{if } y = 0, \\ +\infty & \text{otherwise.} \end{cases}
--   $$
--   2. If $x_{\bar s} > 1$ for some $\bar s \in \mathcal S$, then
--   $$
--   f^*(y) = \begin{cases} \dfrac{\alpha}{\gamma}\log\Big(\dfrac{\alpha}{\gamma}\Big) - \dfrac{\alpha}{\gamma} & \text{if } y = \alpha\log(x) \text{ for some } \alpha \in \mathbb R_+, \\ +\infty & \text{otherwise,} \end{cases}
--   $$
--   where $\log(x) = (\log x_{s'})_{s'}$ and $\alpha\log\alpha = 0$ for $\alpha = 0$.
--
--   Substituting this conjugate into the dual (5.6) of the inner minimization yields the exponential-cone program (5.3) of Proposition 5.1.
--
--   **Formalization Note** The second case is stated as two clauses: the value on the ray $\{\alpha \log x : \alpha \ge 0\}$ and the value $+\infty$ off the ray (the $\alpha$ is unique since $\log x \neq 0$). Lean's `Real.log 0 = 0` gives the convention $0 \log 0 = 0$.
--
--   Differences from the source:
--   - reading: "$f : \Delta(\mathcal S) \to \mathbb R$" in (5.4) → `geoMean γ x` defined on all of $\mathbb R^{\mathcal S}$; reason: the proposition's conjugate is the supremum over $p \in \mathbb R^{\mathcal S}$ (p.16 definition, App. D: "$f(p) = 1$, $\forall p \in \mathbb R^{\mathcal S}$"); restricting $f$ to $\Delta(\mathcal S)$ would change $f^*$ and make the printed values false.
--   - encoding: the case-defined value on and off the ray → two clauses (value at $\alpha \log x$ for each $\alpha \ge 0$; $+\infty$ when $y$ is not of that form); reason: same statement.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, Proposition 5.2, p.17; proof in App. D, p.30

import Mathlib
import Definitions.Def_ConvexRMDP_Supplement_conj
import Definitions.Def_ConvexRMDP_Supplement_geoMean

namespace ConvexRMDP

namespace Supplement

/-- **Proposition 5.2** (Grand-Clément & Petrik, arXiv:2209.10187v2, p.17; proof in App. D, p.30).
Let `x ∈ [1,+∞)^S` and `f(p) = ∏_{s'} x_{s'}^{γ p_{s'}}` as in (5.4). If `x = (1,…,1)`, then
`f*(y) = −1` if `y = 0` and `+∞` otherwise. When `x_{s̄} > 1` for some `s̄ ∈ S`, then
`f*(y) = (α/γ) log(α/γ) − α/γ` if `y = α log(x)` for some `α ∈ ℝ₊`, and `+∞` otherwise
(convention `α log α = 0` for `α = 0`).

**Formalization Note.** `f` is `geoMean γ x`, defined on all of `ℝ^S`, and `f*` is `conj`, the
supremum over all of `ℝ^S` (App. D). `log(x)` is the vector `(log x_{s'})_{s'}`. Lean's
`Real.log 0 = 0` gives the convention `0 log 0 = 0`. `γ ∈ (0,1)` is the discount factor. -/
theorem proposition_5_2 {S : Type*} [Fintype S] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (x : S → ℝ) (hx : ∀ s, 1 ≤ x s) :
    (x = (fun _ => 1) → ∀ y : S → ℝ,
        conj (fun p => ((geoMean γ x p : ℝ) : EReal)) y =
          if y = 0 then ((-1 : ℝ) : EReal) else ⊤) ∧
      ((∃ s, 1 < x s) →
        (∀ α : ℝ, 0 ≤ α →
          conj (fun p => ((geoMean γ x p : ℝ) : EReal)) (fun s => α * Real.log (x s)) =
            (((α / γ) * Real.log (α / γ) - α / γ : ℝ) : EReal)) ∧
        (∀ y : S → ℝ, (¬ ∃ α : ℝ, 0 ≤ α ∧ y = fun s => α * Real.log (x s)) →
          conj (fun p => ((geoMean γ x p : ℝ) : EReal)) y = ⊤)) := by sorry

end Supplement

end ConvexRMDP
