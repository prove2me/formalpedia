-- Prove2me | Theorems.Thm_ApproxIC_UpperBound_lemma_1
-- name    : ApproxIC.UpperBound.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:20.332001+00:00
-- url     : https://prove2.me/theorems/6e3681c4-61a3-480b-a3b0-40e655c64199
-- title:
--   Lemma 1, p. 18 — weak duality: Π(m) ≤ Φ₁(λ) + Φ₂(λ) for every m ∈ M_path(ε) and every dual-feasible λ
-- statement:
--   Assume the standing density assumptions and fix a path $(\mu,\nu_0,v^\star,w)$ and $\varepsilon\ge 0$. Let $\lambda:[\mu,\bar v]\to\mathbb R_+$ be feasible for the dual problem (D):
--   $$\lambda(v)=f(v)\ \text{a.e. on }[\nu_0,\bar v],\qquad \lambda(v)=f(v)+\dot w(v)\lambda(w(v))\ \text{a.e. on }[\mu,\nu_0],$$
--   with $\lambda$ integrable on $[\mu,\bar v]$ and $\Delta^+$ integrable on $[0,\bar v]$. Then every mechanism $m\in\mathcal M_{\text{path}}(\varepsilon)$ satisfies
--   $$\Pi(m)\le\Phi_1(\lambda)+\Phi_2(\lambda),\qquad \Phi_1(\lambda)=\varepsilon\int_\mu^{\bar v}\lambda(v)\,dv,\quad \Phi_2(\lambda)=\int_0^{\bar v}\Big(vf(v)-\dot w(v)\,(w(v)-v)\,\lambda(w(v))\,\mathbf 1_{\{v\in[0,\nu_0]\}}\Big)^+dv .$$
--   Taking the supremum over $m$ and the minimum over $\lambda$ gives $\Pi^\star(\mathcal M_{\text{path}}(\varepsilon))\le\Pi^\star(\mathcal D)$.
--
--   This is the duality step that turns the revenue question into bounding the two terms $\Phi_1$ and $\Phi_2$.
--
--   **Formalization Note** The paper's statement prints $(v-w(v))$ in $\Phi_2$; its proof (p. 39) and Lemma 4 have $(w(v)-v)$, which is used here. The two integrability hypotheses are disclosed additions: the paper's minimum ranges over $\lambda$ with a finite objective, and Lean's Bochner integral of a non-integrable function is $0$. The inequality of optimal values is stated in its $\forall m\,\forall\lambda$ form, which is equivalent and avoids `sSup`/`sInf`.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 18, Lemma 1

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Path

namespace ApproxIC.UpperBound

open MeasureTheory

theorem lemma_1 (M : Model) (hM : M.Standing) (P : Path M) (ε : ℝ) (hε : 0 ≤ ε)
    (lam : ℝ → ℝ) (hlam : DualFeasible M P lam)
    (hint1 : IntegrableOn lam (Set.Icc P.mu M.vbar))
    (hint2 : IntegrableOn (fun v => max 0 (Delta M P lam v)) (Set.Icc 0 M.vbar)) :
    ∀ m ∈ MpathSet M P ε, revenue M m ≤ Phi1 M P ε lam + Phi2 M P lam := by sorry

end ApproxIC.UpperBound
