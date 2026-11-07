-- Prove2me | Theorems.Thm_BddExp3SUM_lemma_2
-- name    : BddExp3SUM.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:31.60051+00:00
-- url     : https://prove2.me/theorems/783810cf-7fbe-4be6-bfd9-0f2ca62589b8
-- title:
--   Lemma 2: $T_d<2s_dn^2$, at most $n/s_{i,d}\le n/s_d$ represented cosets, and $s_M>\sqrt n/2\ge n^{1/4}$
-- statement:
--   For a fixed subinstance and each $d\in\mathcal D$:
--
--   1. the number $T_d$ of triples in $U_1\times U_2\times U_3$ with sum in $H_d$ satisfies $T_d<2s_dn^2$;
--   2. the number of $H_d$-cosets represented in $U_i$ is at most $n/s_{i,d}\le n/s_d$.
--
--   Moreover
--
--   $$s_M>\sqrt n/2\ge n^{1/4}.$$
--
--   Here $s_{i,d}$ is computed from the original list $S_i$, not from $U_i$. The first clause controls false positives of every sum order; the second controls the number of hash classes.
--
--   **Formalization Note** The standing assumptions of p.2 are collected in the structure `Subinst`.
--
--   Differences from the source:
--   - encoding: s_{i,d}, constant on U_i → the supremum of s_{i,d}(x) over x ∈ U_i (sVal); reason: U_i is nonempty and the value is constant on it, so the two agree (proved in the sanity file)
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), Lemma 2, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_BddExp3SUM_Profiles

namespace BddExp3SUM

/-- Lemma 2, p.3 (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission, manuscript sha256 19546c9a…).

**Formalization Note.** `c` and `s` count in the original lists `S i`; `T_d` and the represented cosets
are in the subinstance `U i`. All divisions are in `ℝ`. -/
theorem lemma_2 {M r n : ℕ} {S U : Fin 3 → Finset (Grp M r)} (h : Subinst M r n S U) :
    (∀ d ∈ Dvs M,
      ((countIn U d : ℝ) < 2 * sMin S U d * (n : ℝ) ^ 2) ∧
      ∀ i, (cosetsRepresented (U i) d : ℝ) ≤ (n : ℝ) / sVal S U i d ∧
        (n : ℝ) / sVal S U i d ≤ (n : ℝ) / sMin S U d) ∧
    √(n : ℝ) / 2 < sMin S U M ∧ (n : ℝ) ^ ((1 : ℝ) / 4) ≤ √(n : ℝ) / 2 := by sorry

end BddExp3SUM
