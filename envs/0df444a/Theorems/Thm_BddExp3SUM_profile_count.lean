-- Prove2me | Theorems.Thm_BddExp3SUM_profile_count
-- name    : BddExp3SUM.profile_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:50.130243+00:00
-- url     : https://prove2.me/theorems/53d902c9-f736-4e75-832f-529b9259074c
-- title:
--   §2: at most $(1+\lfloor\log_2 n\rfloor)^L$ profiles per list; each original triple lies in exactly one subinstance
-- statement:
--   Let $S_1,S_2,S_3\subseteq G=\mathbb Z_M^r$ have size at most $n$. Then each list has at most
--
--   $$(1+\lfloor\log_2n\rfloor)^L$$
--
--   distinct profile vectors $(s_{i,d}(x))_{d\in\mathcal D}$, and every triple $(x_1,x_2,x_3)\in S_1\times S_2\times S_3$ belongs to exactly one subinstance, that is, to exactly one triple of profile classes.
--
--   The count bounds the number of subinstances the algorithm has to process, and the partition is what makes it enough to find a witness in one subinstance.
--
--   Differences from the source:
--   - generalization: the standing assumptions of p.2 (n ≥ 16, R ≥ M, |S_i| > √n) → only |S_i| ≤ n; reason: the two claims do not use the others; the source’s setting is a special case
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), §2, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_BddExp3SUM_Profiles

namespace BddExp3SUM

/-- §2, p.2 (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission, manuscript sha256 19546c9a…): "There
are at most `(1 + ⌊log₂ n⌋)^L` profiles per list." and "Every original triple belongs to exactly one
such subinstance."

**Formalization Note.** `S i` are finite subsets of `G = Z_M^r` of size at most `n`. Neither clause
needs the other standing assumptions of p.2, which are therefore not hypotheses here. -/
theorem profile_count {M r n : ℕ} (S : Fin 3 → Finset (Grp M r)) (hS : ∀ i, (S i).card ≤ n) :
    (∀ i, profileCount (S i) ≤ (1 + Nat.log 2 n) ^ Lcard M) ∧
    ∀ x : Fin 3 → Grp M r, (∀ i, x i ∈ S i) →
      ∃! U : Fin 3 → Finset (Grp M r), IsProfileTriple S U ∧ ∀ i, x i ∈ U i := by sorry

end BddExp3SUM
