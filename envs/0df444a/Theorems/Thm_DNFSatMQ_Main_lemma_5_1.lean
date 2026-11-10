-- Prove2me | Theorems.Thm_DNFSatMQ_Main_lemma_5_1
-- name    : DNFSatMQ.Main.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:33:28.427529+00:00
-- url     : https://prove2.me/theorems/44af5aad-b2d3-474f-bbbe-a4e965a489e2
-- title:
--   Lemma 5.1 — single-scan guarantee: both coordinate counts are at most w with probability ≥ 1 − δ
-- statement:
--   Fix a term $c_\star$ in a representation $T$ of $f$ with at most $s$ terms, and let $F = f^{-1}(1)$. For $R \ge |F|/|C_\star|$ and $\delta\in(0,1)$ let
--   $$w = \min\Big\{n,\ \Big\lceil a_0\log_2\frac{2sR}{\delta}\Big\rceil\Big\},$$
--   where $a_0>0$ is a sufficiently large absolute constant. Draw $x\sim U_{C_\star}$ and run $\mathrm{Scan}(x)$ with a uniform permutation. The returned conjunction $c$ always contains $x$, and with probability at least $1-\delta$
--   $$|\mathrm{Fix}(c_\star)\cap\mathrm{Free}(c)| \le w,\qquad |\mathrm{Fix}(c)\cap\mathrm{Free}(c_\star)|\le w.$$
--   "Sufficiently large" is stated as: there is $A > 0$ such that the conclusion holds for every $a_0\ge A$ (the paper's proof shows $A = 40$ works). This is the guarantee the densifier (Theorem 7.1) applies to each heavy term.
--
--   Differences from the source:
--   - encoding: a term: literals on distinct variables → a partial assignment `Conj n = Fin n → Option Bool`; reason: §2 defines terms as noncontradictory; same objects
--   - encoding: coordinates [n] = {1, …, n} and bits {0, 1} → `Fin n` (coordinates 0, …, n−1) and `Bool`; reason: Lean convention; same instances
--   - reading: "a₀ > 0 is a sufficiently large absolute constant" → ∃ A > 0, ∀ a₀ ≥ A; reason: the standard meaning; stronger than "for some a₀"; the proof shows every a₀ ≥ 40 works
--   - encoding: log₂, ⌈·⌉ → `Real.logb 2`, `Nat.ceil`; reason: the argument 2sR/δ exceeds 2, so the ceiling is of a positive number
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Lemma 5.1, p. 14 (PDF 15)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Scan

namespace DNFSatMQ.Main

/-- Lemma 5.1 (p. 14): "a₀ > 0 is a sufficiently large absolute constant" is read as "for every
`a₀ ≥ A`, for some absolute `A > 0`". -/
theorem lemma_5_1 :
    ∃ A : ℝ, 0 < A ∧ ∀ a0 : ℝ, A ≤ a0 →
      ∀ {n s : ℕ} (T : Finset (Conj n)), T.card ≤ s → ∀ cstar ∈ T, ∀ R δ : ℝ,
        ((unionSet T).card : ℝ) / cstar.cube.card ≤ R → 0 < δ → δ < 1 →
        (∀ x ∈ cstar.cube, ∀ π : Equiv.Perm (Fin n), (scanConj (unionSet T) x π).Sat x) ∧
        prob (withPerm cstar.unif)
            {p | (cstar.fix ∩ (scanConj (unionSet T) p.1 p.2).free).card ≤
                    min n ⌈a0 * Real.logb 2 (2 * s * R / δ)⌉₊ ∧
                  ((scanConj (unionSet T) p.1 p.2).fix ∩ cstar.free).card ≤
                    min n ⌈a0 * Real.logb 2 (2 * s * R / δ)⌉₊} ≥ 1 - δ := by sorry

end DNFSatMQ.Main
