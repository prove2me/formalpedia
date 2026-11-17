-- Prove2me | Theorems.Thm_CosDensity_Supplement_theorem_4_3
-- name    : CosDensity.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:18:55.409619+00:00
-- url     : https://prove2.me/theorems/77a75ad4-6a22-4bfe-9f02-6c05d9a2e1e2
-- title:
--   Theorem 4.3 — exact integer density moments in one pass
-- statement:
--   For every integer $p\ge1$ and dimension $d$, there is a one-pass algorithm that computes $M_p(P)$ exactly for every stream $P\subseteq\mathbb R^d$. It stores the vector sum and one degree-$p$ symmetric-tensor counter for every multi-index of weight $p$, hence uses at most
--   $$d+\binom{d+p-1}{p}$$
--   real words.
--
--   Differences from the source:
--   - generalization: input vectors are nonzero by the paper's standing convention → the exact algorithm also covers zero vectors under $\operatorname{unitize}(0)=0$; reason: all monomial identities remain valid and the result specializes to the source
--   - encoding: $O_p(d^p)$ words → at most $d+\binom{d+p-1}{p}$ real words; reason: the proof explicitly counts these monomial counters and the shared vector sum
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), Theorem 4.3, p.14 (PDF p.15)

import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_Supplement_WordStreamAlg

namespace CosDensity.Supplement

set_option autoImplicit false

/-- Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density Moments*,
arXiv:2609.06925 (held version, sha256 f4d4df22…), Theorem 4.3, p.14 (PDF p.15).

For every integer `p ≥ 1`, the vector sum and the `choose (d+p-1) p` degree-`p` symmetric
monomial counters give an exact one-pass algorithm. -/
theorem theorem_4_3 :
    ∀ p : ℕ, 1 ≤ p → ∀ d : ℕ,
      ∃ A : WordStreamAlg (EuclideanSpace ℝ (Fin d)),
        A.words ≤ d + Nat.choose (d + p - 1) p ∧
        ∀ (P : List (EuclideanSpace ℝ (Fin d))) (omega : A.Seed),
          A.estimate omega P = some (CosDensity.moment p P) := by sorry

end CosDensity.Supplement
