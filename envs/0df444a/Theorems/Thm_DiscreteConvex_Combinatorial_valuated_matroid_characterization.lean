-- Prove2me | Theorems.Thm_DiscreteConvex_Combinatorial_valuated_matroid_characterization
-- name    : DiscreteConvex.Combinatorial.valuated_matroid_characterization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T20:29:10.1416+00:00
-- url     : https://prove2.me/theorems/687ca2d8-dad5-4af7-9824-d94d3295c45c
-- title:
--   Theorem 2.32 -- the valuated matroid characterization
-- statement:
--   **Theorem 2.32** (p.72). Let $(V, \mathcal B)$ be a matroid with ground set $V$ and base family $\mathcal B$. A function $\omega : \mathcal B \to \mathbb R$ is a valuation if and only if for **every** linear functional $p : V \to \mathbb R$, the maximizers of the perturbed function $\omega[-p]$ form the base family of a matroid — i.e. this maximizer set is nonempty and again satisfies the simultaneous exchange axiom (B).
--
--   The universal quantifier over $p$ carries the entire content of the statement: fixing a single $p$ (or even finitely many) is a strictly weaker claim, since the maximizer set of any function restricted to a finite family trivially satisfies (B) whenever it happens to be a singleton or the whole family. It is this "robust local optimality under every linear perturbation" property that connects valuated matroids to the M-convex functions developed in the rest of the book, and that makes them the natural discrete analogue of concave functions on a matroid's base polytope.
--
--   **Formalization Note.** The book's own proof of this theorem defers to Theorem 6.30 (a special case of the general M-convex local-exchange theorem, developed in chapter 6); this mission states Theorem 2.32 itself as a free-standing formalization target.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.72, Theorem 2.32.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.72, Theorem 2.32

import Mathlib
import Definitions.Def_DiscreteConvex_Combinatorial_ExchangeFamily
import Definitions.Def_DiscreteConvex_Combinatorial_IsValuation
import Definitions.Def_DiscreteConvex_Combinatorial_PerturbedValuation
import Definitions.Def_DiscreteConvex_Combinatorial_MaximizerFamily

namespace DiscreteConvex.Combinatorial

/-- Theorem 2.32 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.72). Let `(V, 𝓑)` be a
matroid with ground set `V` and base family `𝓑`. A function `ω : 𝓑 → ℝ` (given here as
`ω : Finset V → ℝ`, only its values on `𝓑` mattering) is a valuation if and only if for
every `p : V → ℝ` the maximizers of `ω[-p]` form the base family of a matroid, i.e. the
family `MaximizerFamily 𝓑 (PerturbedValuation ω p)` is nonempty and satisfies the
simultaneous exchange axiom (B). -/
theorem valuated_matroid_characterization {V : Type*} [Fintype V] [DecidableEq V]
    (𝓑 : Finset (Finset V)) (hne : 𝓑.Nonempty) (hexch : ExchangeFamily 𝓑) (ω : Finset V → ℝ) :
    IsValuation 𝓑 ω ↔
      ∀ p : V → ℝ, (MaximizerFamily 𝓑 (PerturbedValuation ω p)).Nonempty ∧
        ExchangeFamily (MaximizerFamily 𝓑 (PerturbedValuation ω p)) := by sorry

end DiscreteConvex.Combinatorial
