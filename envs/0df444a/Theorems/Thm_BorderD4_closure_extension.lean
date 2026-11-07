-- Prove2me | Theorems.Thm_BorderD4_closure_extension
-- name    : BorderD4.closure_extension
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:00:48.558006+00:00
-- url     : https://prove2.me/theorems/4b34362b-b904-4a72-9030-889c1cc60ffa
-- title:
--   §2, p.26: extending coefficients to $\overline{F}$ preserves computation and size
-- statement:
--   Let $\overline F$ be an algebraic closure of a field $F$. Extending the scalars of a $\Sigma^{[k]}\Pi\Sigma\Pi^{[\delta]}$ circuit from $F$ to $\overline F$ (or from $F((\varepsilon))$ to $\overline F((\varepsilon))$) preserves its size and maps the polynomial it computes, exactly or in the border sense, to the same polynomial over $\overline F$. Consequently:
--
--   1. lower bounds on exact circuits over $\overline F$ give the same bounds over $F$;
--   2. lower bounds on border circuits over $\overline F$ give the same bounds over $F$.
--
--   This is what removes the assumption that $F$ is algebraically closed from the goal.
--
--   Differences from the source:
--   - encoding: the variables $x_1,\dots,x_N$ → an arbitrary finite nonempty index type; reason: any such type is $[N]$ up to renaming
--   - encoding: the algebraic closure $\overline F$ → any $E$ with `IsAlgClosure F E`; reason: this is exactly an algebraic closure of $F$
--   - encoding: circuit classes and "lower bounds" → for each $s$: if every circuit over $\overline F$ computing $f$ has size at least $s$, so does every circuit over $F$; reason: this is what a lower bound transfer says
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §2, p.26

import Mathlib
import Definitions.Def_BorderD4_SPSP
import Definitions.Def_BorderD4_BorderComputes
import Definitions.Def_BorderD4_laurentMap
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- §2, p.26: "Extending coefficients from a field `F` to its algebraic closure `F̄` preserves an exact or border
circuit computation and its size, so lower bounds over `F̄` imply the corresponding bounds over `F`."
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §2, p.26 (unnumbered).

The four clauses are the exact computation with its size, the border computation with its size, and the lower-bound
transfer for each. -/
theorem closure_extension {F E σ : Type*} [Field F] [Field E] [Algebra F E] [IsAlgClosure F E]
    [Fintype σ] [Nonempty σ] {k δ : ℕ} (_hk : 1 ≤ k) (_hδ : 1 ≤ δ) :
    (∀ C : SPSP F σ k δ,
      (C.map (algebraMap F E)).eval = map (algebraMap F E) C.eval ∧
        (C.map (algebraMap F E)).size = C.size) ∧
    (∀ (C : SPSP (LaurentSeries F) σ k δ) (f : MvPolynomial σ F), BorderComputes C f →
      BorderComputes (C.map (laurentMap (algebraMap F E))) (map (algebraMap F E) f) ∧
        (C.map (laurentMap (algebraMap F E))).size = C.size) ∧
    (∀ (f : MvPolynomial σ F) (s : ℕ),
      (∀ C' : SPSP E σ k δ, C'.eval = map (algebraMap F E) f → s ≤ C'.size) →
        ∀ C : SPSP F σ k δ, C.eval = f → s ≤ C.size) ∧
    (∀ (f : MvPolynomial σ F) (s : ℕ),
      (∀ C' : SPSP (LaurentSeries E) σ k δ, BorderComputes C' (map (algebraMap F E) f) → s ≤ C'.size) →
        ∀ C : SPSP (LaurentSeries F) σ k δ, BorderComputes C f → s ≤ C.size) := by sorry

end BorderD4
