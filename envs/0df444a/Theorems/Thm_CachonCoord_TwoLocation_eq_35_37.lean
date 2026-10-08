-- Prove2me | Theorems.Thm_CachonCoord_TwoLocation_eq_35_37
-- name    : CachonCoord.TwoLocation.eq_35_37
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:55:04.141119+00:00
-- url     : https://prove2.me/theorems/4ae19c6c-647b-46a6-848e-6c4d90dc16ff
-- title:
--   Eqs. (35)–(37), p. 83 — the marginals of Π; every optimum with s_s > 0 has c′(s_r) = h_s, F_r(s_r) = (h_s + β)/(h_r + β)
-- statement:
--   Let $c'(y) = (h_r + \beta)F_r(y) - \beta$. In the two-location base-stock model the supply chain's cost $\Pi(s_r,s_s)$ is differentiable in each base stock, with
--   $$\frac{\partial \Pi(s_r,s_s)}{\partial s_r} = F_s(s_s)\,c'(s_r) + \int_{s_s}^\infty c'(s_r+s_s-x)\,f_s(x)\,dx \qquad (35)$$
--   $$\frac{\partial \Pi(s_r,s_s)}{\partial s_s} = F_s(s_s)\,h_s + \int_{s_s}^\infty c'(s_r+s_s-x)\,f_s(x)\,dx \qquad (36)$$
--   for all $(s_r, s_s) \in \mathbb R^2$. Moreover:
--   1. every optimal policy $\{s_r, s_s\}$ (a minimizer of $\Pi$ over $\mathbb R^2$) with $s_s > 0$ satisfies
--   $$c'(s_r) = h_s, \quad\text{equivalently}\quad F_r(s_r) = \frac{h_s + \beta}{h_r + \beta}; \qquad (37)$$
--   2. the equation $F_r(\tilde s^1_r) = (h_s+\beta)/(h_r+\beta)$ has exactly one solution $\tilde s^1_r$;
--   3. for that $\tilde s^1_r$, the equation $\partial\Pi(\tilde s^1_r, s_s)/\partial s_s = 0$ has exactly one solution $\tilde s^1_s$.
--
--   This identifies the only candidate optimal policy with positive supplier base stock. The retailer's component is the critical fractile $(h_s+\beta)/(h_r+\beta)$, which is the target of the coordinating contract.
--
--   **Formalization Note** Derivatives are stated with HasDerivAt. The integrals against $f_s(x)\,dx$ over $(s_s,\infty)$ are written as integrals against the law of $D_s$ over $(s_s,\infty)$, which is the same quantity when $D_s$ has density $f_s$ and requires no density hypothesis. Clause 3 is the "exists and is unique" claim, with $\partial\Pi/\partial s_s$ written out by (36); the page's supporting remark that $\Pi(\tilde s^1_r, \cdot)$ is strictly convex is not stated as a separate clause.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.8.4, p. 83, Eqs. (35), (36), (37) and the display F_r(s̃¹_r) = (h_s + β)/(h_r + β) with the two existence-and-uniqueness sentences

import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model

open MeasureTheory

namespace CachonCoord.TwoLocation

/-- §6.8.4, p. 83, Eqs. (35)–(37). The partial derivatives of the supply chain's cost are
(35) `∂Π/∂s_r = F_s(s_s) c'(s_r) + ∫_{s_s}^∞ c'(s_r + s_s − x) f_s(x) dx` and
(36) `∂Π/∂s_s = F_s(s_s) h_s + ∫_{s_s}^∞ c'(s_r + s_s − x) f_s(x) dx`
(the integrals against `f_s(x) dx` written as integrals against the law of `D_s` over
`(s_s, ∞)`); every optimal policy with `s_s > 0` has `c'(s_r) = h_s` (37), i.e.
`F_r(s_r) = (h_s + β)/(h_r + β)`; the solution `s̃¹_r` of that equation exists and is unique, and
then `∂Π(s̃¹_r, s_s)/∂s_s = 0` has exactly one solution `s̃¹_s`. -/
theorem eq_35_37 (M : Model) :
    (∀ sr ss : ℝ, HasDerivAt (fun x => M.Pi x ss)
      (M.FS ss * M.cDeriv sr + ∫ x in Set.Ioi ss, M.cDeriv (sr + ss - x) ∂M.lawS) sr) ∧
    (∀ sr ss : ℝ, HasDerivAt (fun y => M.Pi sr y)
      (M.FS ss * M.hs + ∫ x in Set.Ioi ss, M.cDeriv (sr + ss - x) ∂M.lawS) ss) ∧
    (∀ sr ss : ℝ, IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (sr, ss) → 0 < ss →
      M.cDeriv sr = M.hs ∧ M.FR sr = (M.hs + M.beta) / (M.hr + M.beta)) ∧
    (∃! s1r : ℝ, M.FR s1r = (M.hs + M.beta) / (M.hr + M.beta)) ∧
    (∀ s1r : ℝ, M.FR s1r = (M.hs + M.beta) / (M.hr + M.beta) →
      ∃! s1s : ℝ, M.FS s1s * M.hs + ∫ x in Set.Ioi s1s, M.cDeriv (s1r + s1s - x) ∂M.lawS = 0) := by sorry

end CachonCoord.TwoLocation
