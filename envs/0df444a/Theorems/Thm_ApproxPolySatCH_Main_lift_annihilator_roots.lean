-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_lift_annihilator_roots
-- name    : ApproxPolySatCH.Main.lift_annihilator_roots
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:13:07.919256+00:00
-- url     : https://prove2.me/theorems/8abbcadd-49a8-49f7-9543-53a01251b5d0
-- title:
--   Claim 10 — Lift every annihilator root
-- statement:
--   Let $f$ be minimally dependent in $n\ge1$ variables over $k$, let $H$ be its irreducible annihilator with the canonical presentation after extending scalars, and take any bounded-degree relations preceding equation (17). Let $h$ be the product of their nonzero leading coefficients. If $a\in\overline k^n$ satisfies $h(a)\ne0$, every root $z\in L$ of the specialized annihilator lifts:
--   $$H(a_1\varepsilon,\ldots,a_n\varepsilon,z)=0\ \Longrightarrow\ \exists x\in V(f,a):\ f_{n+1}(x)=z.$$
--   The hypotheses are algebraic relation identities and canonical evaluation presentations; they do not assume root lifting or integrality of the unlocalized polynomial ring.
--
--   This identifies the remaining coordinate's image on the prescribed fiber.
--
--   Differences from the source:
--   - generalization: The coefficient field is rational or finite. → The algebraic statement is quantified over every field, with the stated algebraic closures and valuation where used.; reason: The algebraic arguments use no restriction on the base field; specializing to a rational or finite field gives the entire source statement.
--   - encoding: The previously chosen canonical H and relation-derived h, with every root lifting into the fiber. → H and the actual relation polynomials are parameters satisfying exactly their source identities; h is computed as their leading-coefficient product.; reason: This exposes the standing data and retains every root, without assuming the desired lifting or unlocalized integrality.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Claim 10, p.20 (PDF p.20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=20

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

theorem lift_annihilator_roots {k : Type} [Field k] {n : ℕ}
    (hn : 1 ≤ n) (f : Fin (n + 1) → Poly k n)
    (hf : MinimallyDependent f)
    (H : Poly k (n + 1)) (hH : AnnihilatorPresentation f H) (r : LocalizationRelations f)
    (a : Fin n → Constants k)
    (ha : MvPolynomial.eval₂ (algebraMap k (Constants k)) a (localizationProduct r) ≠ 0) :
    ∀ z : ValuedClosure k, specializedAnnihilator H a z = 0 →
      ∃ x ∈ prescribedFiber f a, evaluateValued (f (Fin.last n)) x = z := by sorry

end ApproxPolySatCH.Main
