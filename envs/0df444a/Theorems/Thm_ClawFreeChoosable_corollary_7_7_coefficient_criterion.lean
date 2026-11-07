-- Prove2me | Theorems.Thm_ClawFreeChoosable_corollary_7_7_coefficient_criterion
-- name    : ClawFreeChoosable.corollary_7_7_coefficient_criterion
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:46:04.288186+00:00
-- url     : https://prove2.me/theorems/85ddc5fb-0a2c-4d85-b1dd-3f380202286d
-- title:
--   Corollary 7.7 — coefficient criterion for precolouring extension
-- statement:
--   Let $G$ be a finite graph with a linear order on $V(G)$, let $Z \subseteq V(G)$, and let $\phi$ be a proper colouring of $G[Z]$ with real colours. Let
--   $$P_{G,\phi} = \prod_{\substack{uv \in E(G - Z)\\ u < v}} (x_v - x_u) \prod_{\substack{vz \in E(G)\\ v \notin Z,\ z \in Z}} (x_v - \phi(z))$$
--   in the variables $x_v$, $v \in V(G) \setminus Z$. Suppose nonnegative integers $d(v)$, $v \notin Z$, satisfy
--   $$\sum_{v \notin Z} d(v) = \deg P_{G,\phi} \quad\text{and}\quad \Big[\prod_{v \notin Z} x_v^{d(v)}\Big] P_{G,\phi} \ne 0.$$
--   Then for every list assignment $L$ on $V(G) \setminus Z$ with $|L(v)| \ge d(v) + 1$ there is a proper colouring $f$ of $G$ with $f = \phi$ on $Z$ and $f(v) \in L(v)$ for $v \notin Z$.
--
--   This is the form of the Combinatorial Nullstellensatz used for cobipartite graphs and graphs of interval type.
--
--   Differences from the source:
--   - encoding: colours of a finite list-colouring instance, identified injectively with real numbers (p.12) → ϕ : V → ℝ and L : V → Finset ℝ; reason: the paper makes this identification whenever graph polynomials are used; same instances
--   - encoding: a linear order on V(G), deg P, the coefficient [∏ x_v^{d(v)}]P → LinearOrder V, MvPolynomial.totalDegree, MvPolynomial.coeff at the exponent d; reason: Lean convention; same values
--   - encoding: ϕ on Z and L on V(G) \ Z → total maps on V of which only ϕ on Z and L off Z are read; reason: Lean convention; same instances
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Corollary 7.7, p.12 (PDF p.15)

import Mathlib
import Definitions.Def_ClawFreeChoosable_precolouredGraphPolynomial

set_option autoImplicit false

open Classical

namespace ClawFreeChoosable

/-- **Corollary 7.7** (Mishra, Narayanan N, Shankar, *Claw-free perfect graphs are chromatic-choosable*, arXiv:2611.01068v1, p.12). Let `Z ⊆ V(G)`, and let `ϕ` be a proper coloring of `G[Z]`.
Define `P_{G,ϕ} = ∏_{uv ∈ E(G − Z), u < v} (x_v − x_u) ∏_{vz ∈ E(G), v ∉ Z, z ∈ Z} (x_v − ϕ(z))` in
the variables indexed by `V(G) \ Z`. Suppose that nonnegative integers `d(v)`, `v ∉ Z`, satisfy
`∑_{v ∉ Z} d(v) = deg P_{G,ϕ}` and `[∏_{v ∉ Z} x_v^{d(v)}] P_{G,ϕ} ≠ 0`. Then `ϕ` extends to a
proper coloring of `G` from every list assignment on `V(G) \ Z` with `|L(v)| ≥ d(v) + 1`.

**Formalization Note.** Colours are real numbers (the paper identifies colours injectively with
reals whenever graph polynomials are used, p.12). The linear order on `V(G)` is a
`LinearOrder V`, the degree is `totalDegree`, and the coefficient of `∏ x_v^{d(v)}` is `coeff` at
the finitely supported exponent `d`. `ϕ` and `L` are total maps on `V`; only `ϕ` on `Z` and `L`
off `Z` are read. -/
theorem corollary_7_7_coefficient_criterion {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (Z : Set V) (ϕ : V → ℝ) (hϕ : ∀ u ∈ Z, ∀ v ∈ Z, G.Adj u v → ϕ u ≠ ϕ v)
    (d : {v // v ∉ Z} → ℕ)
    (hdeg : ∑ v, d v = (precolouredGraphPolynomial G Z ϕ).totalDegree)
    (hcoeff : (precolouredGraphPolynomial G Z ϕ).coeff (Finsupp.equivFunOnFinite.symm d) ≠ 0)
    (L : V → Finset ℝ) (hL : ∀ v : {v // v ∉ Z}, d v + 1 ≤ (L v.1).card) :
    ∃ f : V → ℝ, (∀ u v, G.Adj u v → f u ≠ f v) ∧ (∀ z ∈ Z, f z = ϕ z) ∧
      ∀ v, v ∉ Z → f v ∈ L v := by sorry

end ClawFreeChoosable
