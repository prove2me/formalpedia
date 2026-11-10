-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_positive_valuation_root
-- name    : ApproxPolySatCH.Main.positive_valuation_root
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:12:30.430201+00:00
-- url     : https://prove2.me/theorems/2e0dd37f-cf0b-432e-995b-b5322a11beae
-- title:
--   Claim 8 — Controlled-valuation root
-- statement:
--   Let $f$ be minimally dependent in $n\ge1$ variables over a field $k$, and let $H$ be its irreducible annihilator with the canonical scalar-extension presentation. Let $L=\overline{\overline k(\varepsilon)}$ carry an extension of the epsilon-adic valuation $\nu$, and put $D_H=\deg H$. There are one coordinate permutation and one nonzero homogeneous $G\in k[Y_1,\ldots,Y_n]$ of degree at most $D_H-1$, such that every $a\in\overline k^n$ with $G(a)\ne0$ satisfies
--   $$\exists z\in L:\ H(a_1\varepsilon,\ldots,a_n\varepsilon,z)=0.$$
--   For the same permutation and the same exceptional polynomial, if the APS input is positive, one can choose such a root with $\nu(z)>0$.
--
--   This retains both the unconditional root clause and the positive-valuation clause, including small characteristic.
--
--   Differences from the source:
--   - generalization: The coefficient field is rational or finite. → The algebraic statement is quantified over every field, with the stated algebraic closures and valuation where used.; reason: The algebraic arguments use no restriction on the base field; specializing to a rational or finite field gives the entire source statement.
--   - encoding: One permutation and homogeneous exceptional polynomial work for all parameter vectors, in the valued algebraic closure. → The permutation renames H by its inverse, homogeneity is stated on support, and roots lie in the fixed closure of the rational function field.; reason: Inverse renaming preserves H(f)=0 for the permuted tuple, and the font-distinguished valued closure is represented separately from the constant closure.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Claim 8, p.19 (PDF p.19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=19

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

theorem positive_valuation_root {k : Type} [Field k] {n : ℕ}
    (hn : 1 ≤ n) (f : Fin (n + 1) → Poly k n)
    (hf : MinimallyDependent f)
    (H : Poly k (n + 1)) (hH : AnnihilatorPresentation f H) (v : EpsilonValuation k) :
    ∃ (sigma : Equiv.Perm (Fin (n + 1))) (G : Poly k n), G ≠ 0 ∧
      (∃ r : ℕ, r ≤ H.totalDegree - 1 ∧ ∀ e ∈ G.support, ∑ j, e j = r) ∧
      ∀ a : Fin n → Constants k, MvPolynomial.eval₂ (algebraMap k (Constants k)) a G ≠ 0 →
        (∃ z : ValuedClosure k, specializedAnnihilator (MvPolynomial.rename sigma.symm H) a z = 0) ∧
        (APS f → ∃ z : ValuedClosure k,
          specializedAnnihilator (MvPolynomial.rename sigma.symm H) a z = 0 ∧ 0 < v.val z) := by sorry

end ApproxPolySatCH.Main
