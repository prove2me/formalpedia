-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_7_3
-- name    : ExactPatternStream.lemma_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:12.536195+00:00
-- url     : https://prove2.me/theorems/202ca885-9052-4e73-8642-2328f8b7d42c
-- title:
--   Lemma 7.3 — $R_s$ creates a false occurrence with probability $O((n/m)\log d\log(md)/|F|)$
-- statement:
--   Let $F$ be a finite field, $d\ge3$, and $P\in(F^d)^m$, $T\in(F^d)^n$, $1\le m\le n$. If $s$ is uniform in $(F^2)^D$, then
--   $$\Pr\big[\mathrm{Occ}(P,T)\ne\mathrm{Occ}(R_s(P),R_s(T))\big]=O\Big(\frac nm\cdot\frac{\log d\,\log(md)}{|F|}\Big).$$
--   Reusing one seed pair per round keeps the seed short, at the cost of only logarithmic factors.
--
--   Differences from the source:
--   - encoding: $O(\cdot)$ → one absolute $K$ before all variables, with $\log_2$; reason: the same bounds up to a constant
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 7.3, p.18 (PDF 19)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_LinearMaps
import Definitions.Def_ExactPatternStream_HashFamily

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 7.3, p.18 (PDF 19).

For a finite field `F`, `d ≥ 3`, `P ∈ (F^d)^m`, `T ∈ (F^d)^n`, `1 ≤ m ≤ n`, a uniform seed `s ∈ (F²)^D` of Definition 7.2 has `Pr[Occ(P, T) ≠ Occ(R_s(P), R_s(T))] = O((n/m) log d log(md)/|F|)`.

**Formalization Note.** `R_s` is applied coordinatewise to the symbols. It returns the list of its two output coordinates. `O(·)` is an absolute `K` before the field and `d`; `log₂`. -/
theorem lemma_7_3 : ∃ K : ℝ, ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F] (d : ℕ)
    (P T : List (Fin d → F)), 3 ≤ d → 1 ≤ P.length → P.length ≤ T.length →
    unifProb (fun s : Fin (roundsD d) → F × F => occ P T ≠ occ (P.map (rs s)) (T.map (rs s))) ≤
      K * ((T.length : ℝ) / P.length) * Real.logb 2 d * Real.logb 2 ((P.length : ℝ) * d) /
        (Fintype.card F : ℝ) := by sorry

end ExactPatternStream
