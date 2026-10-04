-- Prove2me | Theorems.Thm_EkelandVP_Constraints_tangent_curve
-- name    : EkelandVP.Constraints.tangent_curve
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:51:55.07878+00:00
-- url     : https://prove2.me/theorems/c3919533-e5dd-45b6-9ebf-378bbbb6ff20
-- title:
--   §3, proof of Lemma 3.2, (3.16), p. 331 — a C¹ feasible curve u: [0, τ] → 𝒞 with u(0) = v and u′(0) = h
-- statement:
--   Let $V$ be a real Banach space and $G_1,\dots,G_m:V\to\mathbb R$ be $C^1$, the first $p$ being equality constraints and the others inequality constraints, with feasible set $\mathcal C$ (3.2). Let $v\in\mathcal C$ be a point at which the derivatives $\big(G_i'(v)\big)_{i\in I(v)}$ of the saturated constraints are linearly independent (assumption (3.4) at $v$). Let $h\in V$ satisfy
--   $$\langle G_i'(v),h\rangle=0\quad (1\le i\le p), \tag{3.13}$$
--   $$\langle G_i'(v),h\rangle\ge 0\quad (i\in\{p+1,\dots,m\}\cap I(v)). \tag{3.14}$$
--   Then there are $\tau>0$ and a $C^1$ curve $u:[0,\tau]\to\mathcal C$ with
--   $$u(0)=v\qquad\text{and}\qquad \frac{du}{dt}(0)=h. \tag{3.16}$$
--
--   This is the Lyusternik-type step in the proof of Lemma 3.2; the page obtains it "by a standard argument using assumption (3.4) and the implicit function theorem".
--
--   **Formalization Note.** The curve is a function `u : ℝ → V`; only its values on $[0,\tau]$ matter. "$C^1$ on $[0,\tau]$" is `ContDiffOn ℝ 1 u (Set.Icc 0 τ)` and $u'(0)=h$ is the one-sided derivative `HasDerivWithinAt u h (Set.Icc 0 τ) 0`. Regularity is assumed only at the point $v$, which is what the page uses; the standing assumption (3.4) at every feasible point implies it. Constraint $i$ of the page is Lean index $i-1$.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 331, §3, proof of Lemma 3.2, (3.13)–(3.16)

import Mathlib
import Definitions.Def_EkelandVP_Constraints_feasibleSet

namespace EkelandVP.Constraints

/-- Ekeland (1974), §3, proof of Lemma 3.2, (3.16), p. 331: at a feasible point `v` where the
saturated constraint derivatives are linearly independent ((3.4) at `v`), every direction `h` with
`G_i'(v) h = 0` for the equality constraints (3.13) and `G_i'(v) h ≥ 0` for the saturated inequality
constraints (3.14) is the initial velocity of a `C¹` curve `u : [0, τ] → 𝒞` with `u(0) = v`. -/
theorem tangent_curve {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {m : ℕ} (p : ℕ) (G : Fin m → V → ℝ) (hG : ∀ i, ContDiff ℝ 1 (G i))
    (v : V) (hv : v ∈ feasibleSet p G)
    (hli : LinearIndependent ℝ (fun i : {i : Fin m // G i v = 0} => fderiv ℝ (G i) v))
    (h : V)
    (h13 : ∀ i : Fin m, i.val < p → fderiv ℝ (G i) v h = 0)
    (h14 : ∀ i : Fin m, p ≤ i.val → G i v = 0 → 0 ≤ fderiv ℝ (G i) v h) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ u : ℝ → V, u 0 = v ∧
      (∀ t ∈ Set.Icc (0 : ℝ) τ, u t ∈ feasibleSet p G) ∧
      ContDiffOn ℝ 1 u (Set.Icc (0 : ℝ) τ) ∧
      HasDerivWithinAt u h (Set.Icc (0 : ℝ) τ) 0 := by sorry

end EkelandVP.Constraints
