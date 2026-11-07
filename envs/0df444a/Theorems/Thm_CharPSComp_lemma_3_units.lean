-- Prove2me | Theorems.Thm_CharPSComp_lemma_3_units
-- name    : CharPSComp.lemma_3_units
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:11:05.810922+00:00
-- url     : https://prove2.me/theorems/3a5b4726-6839-4544-a0c3-589d6aa0161f
-- title:
--   Lemma 3 (part 2 of 3: units; parts 1, 3: lemma_3_construction, lemma_3_arithmetic) — $\rho^j-\rho^i$ is a unit in $E$
-- statement:
--   This item is the unit clause of Lemma 3; the other clauses are `CharPSComp.lemma_3_construction` and `CharPSComp.lemma_3_arithmetic`.
--
--   Let $R$ be a nonzero commutative ring of prime characteristic $p$, $N=p^r$, and let $(h,\rho)$ be admissible transform data for $N$: $h\in\mathbb F_p[z]$ monic irreducible of degree $d$ and $\rho\in\mathbb F=\mathbb F_p[z]/(h)$ of order at least $L_{\max}$. With $\mathbb F$ embedded in $E=R[z]/(h)$ coefficientwise, for $0\le i<j<L_{\max}$
--   $$\rho^j-\rho^i\ \text{is a unit in }E .$$
--
--   This makes the Vandermonde matrix $V_L$ of the evaluation points invertible over $E$, so interpolation in Lemma 4 is well defined.
--
--   Differences from the source:
--   - encoding: $\rho^j-\rho^i\in E$ via the embedding $\mathbb F\hookrightarrow E$ → `embedF R h (ρ ^ j - ρ ^ i)`; reason: the embedding of Appendix B, p.22: inclusion $\mathbb F_p\hookrightarrow R$ on the coefficients of the degree-$<d$ representative
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), Lemma 3, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_CharPSComp_tableWords

open Polynomial

namespace CharPSComp

/-- Lemma 3 (Transform data and extension arithmetic), part (ii): unit differences, Zhu, *Faster
Power Series Composition in Fixed Positive Characteristic*, STOC 2027 submission (manuscript sha256
e63e0527…), p.8 (PDF p.9). Companion items: `lemma_3_construction` (part (i)) and
`lemma_3_arithmetic` (part (iii)).

"For 0 ≤ i < j < L_max, the difference ρ^j − ρ^i is a unit in E." Here `R` is a nonzero commutative
ring of characteristic `p`, `N = pʳ`, `h ∈ F_p[z]` is monic irreducible of degree `d`, `ρ ∈ F` has
order at least `L_max`, and `E = R[z]/(h)` with `F` embedded in `E` coefficientwise. -/
theorem lemma_3_units {R : Type*} [CommRing R] [Nontrivial R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (r : ℕ) (h : (ZMod p)[X]) (ρ : AdjoinRoot h) (hT : IsTransformPair p (p ^ r) h ρ)
    (i j : ℕ) (hij : i < j) (hj : j < Lmax p (p ^ r)) :
    IsUnit (embedF R h (ρ ^ j - ρ ^ i)) := by sorry

end CharPSComp
