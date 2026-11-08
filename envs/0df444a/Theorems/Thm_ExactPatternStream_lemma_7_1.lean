-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_7_1
-- name    : ExactPatternStream.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:23.315097+00:00
-- url     : https://prove2.me/theorems/0e3bac13-080f-4bc0-bf2f-d91fd24d16fb
-- title:
--   Lemma 7.1 — one random map $M_{a,b}$ creates a false occurrence with probability $O((n/m)\log(2m)/|F|)$
-- statement:
--   Let $F$ be a finite field and $P\in(F^3)^m$, $T\in(F^3)^n$, $1\le m\le n$. For a uniformly random $(a,b)\in F^2$,
--   $$\Pr\big[\mathrm{Occ}(P,T)\ne\mathrm{Occ}(M_{a,b}(P),M_{a,b}(T))\big]=O\Big(\frac nm\cdot\frac{\log(2m)}{|F|}\Big).$$
--   A single random linear map thus avoids all false positives at once with small error.
--
--   Differences from the source:
--   - encoding: $O(\cdot)$ → one absolute $K$ before all variables, with $\log_2$; reason: the same bounds up to a constant
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 7.1, p.17 (PDF 18)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_LinearMaps
import Definitions.Def_ExactPatternStream_HashFamily

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 7.1, p.17 (PDF 18).

For a finite field `F` and vector strings `P ∈ (F³)^m`, `T ∈ (F³)^n`, `1 ≤ m ≤ n`, a uniform `(a, b) ∈ F²` has `Pr[Occ(P, T) ≠ Occ(M_{a,b}(P), M_{a,b}(T))] = O((n/m) log(2m)/|F|)`.

**Formalization Note.** `O(·)` is an absolute `K` before the field; `log₂`; the quotients are real. -/
theorem lemma_7_1 : ∃ K : ℝ, ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (P T : List (Fin 3 → F)), 1 ≤ P.length → P.length ≤ T.length →
    unifProb (fun s : F × F => occ P T ≠ occ (P.map (mab s.1 s.2)) (T.map (mab s.1 s.2))) ≤
      K * ((T.length : ℝ) / P.length) * Real.logb 2 (2 * P.length) / (Fintype.card F : ℝ) := by sorry

end ExactPatternStream
