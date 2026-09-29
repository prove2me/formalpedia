-- Prove2me | Theorems.Thm_FeynmanWick_card_pairings
-- name    : FeynmanWick.card_pairings
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T03:17:25.014032+00:00
-- url     : https://prove2.me/theorems/314da3e3-3b81-427d-9c2f-da69cf53fa12
-- title:
--   The number of pairings of $2n$ labels is $(2n-1)!!$
-- statement:
--   For every $n \in \mathbb{N}$, the number of pairings of $2n$ labels — partitions of
--   $\{0,\dots,2n-1\}$ into $n$ unordered pairs, equivalently fixed-point-free involutions of that
--   set — is the double factorial
--
--   $$ \# P_n \;=\; (2n-1)!! \;=\; (2n-1)\cdot(2n-3)\cdots 3\cdot 1, $$
--
--   with the empty product convention $\# P_0 = 1$.
--
--   This is the counting argument the source uses: the first label can be paired with any of the
--   remaining $2n-1$ labels, the first still unpaired label with any of $2n-3$, and so on. It is the
--   combinatorial half of Wick's theorem, independent of any measure theory, and it is what makes the
--   single-variable moment $(2n-1)!!\,\langle x^2\rangle^n$ agree with the sum over diagrams.
-- source:
--   Feynman diagram, Wikipedia (revision captured 2026-09-20), https://en.wikipedia.org/wiki/Feynman_diagram, sections 'Wick theorem' and 'Higher Gaussian moments — completing Wick's theorem'

import Mathlib
import Definitions.Def_FeynmanWickPairings
open MeasureTheory ProbabilityTheory

namespace FeynmanWick

theorem card_pairings (n : ℕ) :
    (pairings n).card = Nat.doubleFactorial (2 * n - 1) := by sorry

end FeynmanWick
