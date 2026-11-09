-- Prove2me | Theorems.Thm_BarelyTestable_LowerBound_square_slack
-- name    : BarelyTestable.LowerBound.square_slack
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:22:07.750803+00:00
-- url     : https://prove2.me/theorems/a3bb7991-50a7-422f-9396-55ec4f2aab18
-- title:
--   Lemma 3.2 — complete square slack classification
-- statement:
--   For every $m\ge9$, every realization of the two label maps and shared table, and either sign $\sigma\in\{+1,-1\}$, each valid square satisfies the following classification:
--
--   $$\mathrm{slack}(F^{(\sigma)})=\sigma/2^{2m^2+2}\quad\text{at action-coordinate squares based at centers},$$
--   $$\mathrm{slack}(F^{(\sigma)})\ge0\quad\text{at every other square}.$$
--
--   This is pointwise over all realizations, covers both orders of the spanning coordinates, and includes action squares away from centers, control squares and mixed squares.
--
--   Differences from the source:
--   - encoding: two action bits and two halves with m blocks of m coordinates → Coord m = Bool ⊕ ((Fin m × Fin m) ⊕ (Fin m × Fin m)); reason: this coordinate type has 2m²+2 elements and coordEquiv explicitly renames it to Fin (2m²+2)
--   - reading: large enough m → m ≥ 9; reason: §3.2.1 p.16 proves Lemma 3.2 for every m ≥ 9, uniformly over all realizations and both signs
--   - encoding: sign σ ∈ {+1,−1} → a Boolean selecting +1 or −1; reason: both possible signs are quantified, with true selecting YES
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Lemma 3.2, p. 13 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Construction

set_option autoImplicit false

namespace BarelyTestable.LowerBound

open NonmonotoneSubmod.Shared MeasureTheory

/-- Lemma 3.2, p.13; m ≥ 9 is supplied by §3.2.1, p.16. -/
theorem square_slack {m : ℕ} (hm : 9 ≤ m) (r : Sample m) (sign : Bool)
    (S : Cube (Coord m)) (u v : Coord m) (hv : ValidSquare S u v) :
    let special := Center r.1 r.2.1 (xPart S) (yPart S) ∧
      ((u = actionA ∧ v = actionB) ∨ (u = actionB ∧ v = actionA))
    (special → slack (hard r sign) S u v = (if sign then (1 : ℝ) else -1) / 2 ^ dimension m) ∧
    (¬special → 0 ≤ slack (hard r sign) S u v) := by sorry

end BarelyTestable.LowerBound
