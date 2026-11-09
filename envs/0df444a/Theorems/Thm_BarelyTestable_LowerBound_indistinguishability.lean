-- Prove2me | Theorems.Thm_BarelyTestable_LowerBound_indistinguishability
-- name    : BarelyTestable.LowerBound.indistinguishability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:24:13.92924+00:00
-- url     : https://prove2.me/theorems/b8ab40de-3471-47fd-9716-dcfb582feeba
-- title:
--   Lemma 3.20 — acceptance-gap bound
-- statement:
--   For positive $m$ and any deterministic adaptive procedure $A$ with worst-case budget $q$, let $p_+$ and $p_-$ be its actual acceptance probabilities under the YES and NO laws. Then
--
--   $$|p_+-p_-|\le q^2/2^m+2q/2^{2m^2+2}.$$
--
--   Both probabilities sample the entire independent labels and shared table once per oracle. The table denominator remains the construction dimension when the function is padded.
--
--   Differences from the source:
--   - encoding: two action bits and two halves with m blocks of m coordinates → Coord m = Bool ⊕ ((Fin m × Fin m) ⊕ (Fin m × Fin m)); reason: this coordinate type has 2m²+2 elements and coordEquiv explicitly renames it to Fin (2m²+2)
--   - encoding: independent uniform labels and table entries → uniform counting probability on the full finite product Sample m; reason: every assignment occurs once, giving exactly the independent product law and its pushforward to the constructed real functions
--   - encoding: A(F)=1 → some finite recursively defined run returns accept; reason: Budget ensures this is the actual final decision after at most q queries; it is not a separately supplied acceptance function
--   - generalization: Lemma 3.20, under the standing assumption of §3 (p.11) that m is a large enough integer → every m ≥ 1; reason: the source proof uses no lower bound on m, and the Lean statement specializes to every large m
--   - encoding: F^(+1), F^(−1) → hard r true, hard r false; reason: the Boolean true selects σ = +1 (YES) and false selects σ = −1 (NO)
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Lemma 3.20, p. 26 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Discovery

set_option autoImplicit false

namespace BarelyTestable.LowerBound

open NonmonotoneSubmod.Shared MeasureTheory

/-- Lemma 3.20, p.26: actual acceptance of the recursively defined runs. -/
theorem indistinguishability {m : ℕ} (hm : 1 ≤ m) (A : Procedure (Coord m))
    (q : ℕ) (hbudget : Budget A q) :
    |acceptanceProbability A true - acceptanceProbability A false| ≤
      (q : ℝ)^2 / 2^m + 2*(q : ℝ) / 2^(dimension m) := by sorry

end BarelyTestable.LowerBound
