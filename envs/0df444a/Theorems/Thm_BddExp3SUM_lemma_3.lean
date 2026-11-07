-- Prove2me | Theorems.Thm_BddExp3SUM_lemma_3
-- name    : BddExp3SUM.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:01:04.229869+00:00
-- url     : https://prove2.me/theorems/1f9394dc-008b-4617-9ebd-17b6660feea9
-- title:
--   Lemma 3: fewer than $M^2n/\sigma$ nonempty $\pi$-classes, and at most $(M^2+1)n/\sigma$ blocks
-- statement:
--   For a fixed subinstance with its certificate and for every choice of rows, each $U_i$ has fewer than
--
--   $$M^2n/\sigma$$
--
--   nonempty $\pi$-classes. Cutting each class into blocks of size at most $\sigma$ gives at most $(M^2+1)n/\sigma$ blocks.
--
--   The first bound is the class bound supplied by the single divisor $e$; it is independent of the rows.
--
--   Differences from the source:
--   - reading: "Cutting each such class into blocks of size at most σ" → a class of size a is cut into exactly ⌈a/σ⌉ blocks (IsBlockCut); reason: the bound is false for an arbitrary partition into small pieces (singletons give |U_i| blocks); the proof bounds the number of blocks by "the number of classes plus |U_i|/σ", which is this cut
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), Lemma 3, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_BddExp3SUM_Blocks

namespace BddExp3SUM

/-- Lemma 3, p.4 (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission, manuscript sha256 19546c9a…).

**Formalization Note.** "Cutting each such class into blocks of size at most σ" is `IsBlockCut`: a
class of size `a` is cut into exactly `⌈a/σ⌉` blocks. -/
theorem lemma_3 {M r n k q e p : ℕ} {S U : Fin 3 → Finset (Grp M r)}
    (h : Cert M r n S U k q e p) (u : Fin (k + q) → Grp M r) (i : Fin 3) :
    (classCount (U i) (piHash h.p_dvd e u) : ℝ) < (M : ℝ) ^ 2 * n / σ M n ∧
    ∀ parts : Finset (Finset (Grp M r)), IsBlockCut (piHash h.p_dvd e u) (U i) (σ M n) parts →
      (parts.card : ℝ) ≤ ((M : ℝ) ^ 2 + 1) * n / σ M n := by sorry

end BddExp3SUM
