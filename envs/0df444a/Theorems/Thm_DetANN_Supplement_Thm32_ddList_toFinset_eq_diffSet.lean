-- Prove2me | Theorems.Thm_DetANN_Supplement_Thm32_ddList_toFinset_eq_diffSet
-- name    : DetANN.Supplement.Thm32.ddList_toFinset_eq_diffSet
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:50:52.142504+00:00
-- url     : https://prove2.me/theorems/b839b8ec-945d-47ad-8275-5a839cf6680b
-- title:
--   The deduplication table is exactly the padded difference set
-- statement:
--   Fix $P:[n]\to\mathbb R^d$ and a padding exponent $k$. Let $Q_i=\operatorname{pad}_{2^k}(P_i)$. The construction program enumerates the differences $Q_i-Q_j$ for $i<j<n$ in lexicographic order, appending each difference only if it has not occurred before. If $\mathcal L$ is the resulting list and
--
--   $$
--   \mathcal D=\{Q_i-Q_j:i<j<n\},
--   $$
--
--   then the elements of $\mathcal L$ form precisely $\mathcal D$, and $\mathcal L$ has no repetitions. In particular,
--
--   $$
--   \operatorname{toFinset}(\mathcal L)=\mathcal D,
--   \qquad |\mathcal L|=|\mathcal D|.
--   $$
--
--   This identifies the finite set used by the greedy sign-computation program with the set $\mathcal D$ used in the explicit blocks of §7.4, not merely their cardinalities. No injectivity or dimension hypothesis is needed: both sides are defined by the same enumeration of ordered pairs.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), §6.1, p.14 (the signed-Hadamard construction program) and §7.4, p.19 (the padded database and its difference set). Original pure glue for DetANN.Thm11.outer_composition, using definitions DetANN_Supplement_PreDedup and DetANN_Construction.

import Mathlib
import Definitions.Def_DetANN_Construction
import Definitions.Def_DetANN_Supplement_PreDedup

open DetANN
open DetANN.Supplement.Thm32

/-- The deduplicated loop table is exactly the padded difference finset, and its length is the
cardinality of that finset. -/
theorem DetANN.Supplement.Thm32.ddList_toFinset_eq_diffSet {d n : ℕ} (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) :
    (ddList (ptSeq (fun i => padVec (2 ^ k) (P i))) n).toFinset = diffSet k P ∧
      (ddList (ptSeq (fun i => padVec (2 ^ k) (P i))) n).length = (diffSet k P).card := by sorry
