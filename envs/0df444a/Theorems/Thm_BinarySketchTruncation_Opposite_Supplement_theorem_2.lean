-- Prove2me | Theorems.Thm_BinarySketchTruncation_Opposite_Supplement_theorem_2
-- name    : BinarySketchTruncation.Opposite.Supplement.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T18:06:50.59647+00:00
-- url     : https://prove2.me/theorems/055e0bf3-2f8d-433d-9a5a-0a200a799ccb
-- title:
--   Theorem 2 — unate evaluation dominance and equality of minimum errors
-- statement:
--   Let Z be uniform on 𝔽₂ⁿ and let f : 𝔽₂ⁿ → {0,1} be unate, including the possibility that f is constant. For every binary k-by-n matrix A and every ordered information set I of size k, the observation Z_I dominates AZ for the function-value experiment. Explicitly, there is one row-stochastic kernel K such that
--
--   $$
--   \Pr\{f(Z)=h,AZ=y\}=\sum_u\Pr\{f(Z)=h,Z_I=u\}K(u,y)
--   \quad(h=0,1).
--   $$
--
--   In addition, for every integer 1 ≤ k ≤ n, writing e_f(s) for the minimum evaluation error over all Boolean decoders,
--
--   $$
--   \min_{A:\operatorname{rank}(A)=k} e_f(AZ)
--    =\min_{I:\lvert I\rvert=k} e_f(Z_I).
--   $$
--
--   Both minima are attained. Thus coordinate projection is optimal both as an experiment about the function value and for its minimum evaluation error; no clause of the source's conclusion is omitted.
--
--   Differences from the source:
--   - encoding: binary vectors, rank-k matrices and k-element information sets → Fin-indexed ZMod 2 vectors, full-row-rank k-by-n matrices and coordinate embeddings with the published invertible-column condition; reason: these are the source objects after its stated removal of dependent rows; orderings of coordinates reindex observations and decoders, and an information set already implies row rank k
--   - encoding: conditional Blackwell dominance for hypothesis f(Z), with the constant case called trivial → one normalized kernel simulates the joint masses of f(Z) and each statistic; reason: for each function value of positive probability its mass cancels to give the conditional comparison; zero-probability hypotheses impose the zero joint-mass equation, so constant functions remain included
--   - encoding: minimum errors over rank-k sketches and k-element coordinate sets → real infima on the finite feasible types, together with explicit witnesses attaining both infima; reason: the constraint 1 ≤ k ≤ n makes both types nonempty, and the additional witnesses retain the source minimum rather than only an unattained infimum
-- source:
--   Robinson D.H. Cung, Adway Girish, Emre Telatar, STOC 2027 submission #341 (October 2026), p. 9 (PDF p. 10), Theorem 2; pp. 10–11 (PDF pp. 11–12), proof; Definition 5 and Eq. (3)

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Supplement_UnateEvaluation

namespace BinarySketchTruncation.Opposite.Supplement

/-- Theorem 2, printed p. 9 (PDF 10): both exact experiment dominance
(including constant f) and equality of the attained rank-k minimum errors.
An information set already implies full row rank; no redundant rank binder is added. -/
theorem theorem_2 {n : ℕ} (f : Vec n → Bool) (hf : IsUnate f) :
    (∀ (k : ℕ) (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n),
      IsInformationSet A e →
        FunctionDominates f (fun z => z ∘ e) (fun z => A.mulVec z)) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ n →
      optimalLinearError f k = optimalProjectionError f k ∧
      (∃ A : Matrix (Fin k) (Fin n) Bit, FullRowRank A ∧
        minimumError f (fun z => A.mulVec z) = optimalLinearError f k) ∧
      (∃ e : Fin k ↪ Fin n,
        minimumError f (fun z => z ∘ e) = optimalProjectionError f k)) := by sorry

end BinarySketchTruncation.Opposite.Supplement
