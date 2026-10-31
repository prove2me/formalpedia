-- Prove2me | Theorems.Thm_CardinalMatching_lemma_12
-- name    : CardinalMatching.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:57.123061+00:00
-- url     : https://prove2.me/theorems/9864f024-2325-46b3-9621-eaf9dbb290c9
-- title:
--   Lemma 12: the modified instance has $n'\le 2kn$ agents and goods (corrected: $k\ge n^4/\varepsilon$, $k\ge n^4$)
-- statement:
--   Let $I'$ be the modified instance built from admissible parameters (see `ModParams`). Then $I'$ has as many agents as goods, and their number $n'=|A'|=|G'|$ satisfies
--   $$
--   n'\le 2kn .
--   $$
--   The construction is therefore polynomial in $n$, $k$, which makes the reduction of Theorem 8 polynomial-time.
--
--   **Formalization Note** The equality $|A'|=|G'|$ is stated explicitly: the paper's step 4 asserts it, and with the printed parameter $k\ge n^3/\varepsilon$ it can fail.
--
--   Differences from the source:
--   - correction: k ≥ n³/ε in the construction of I′ (p.8) → k ≥ n⁴/ε and k ≥ n⁴ (ModParams.Admissible); reason: as printed, interpolating agents can outnumber the k/n awesome goods so |A′| = |G′| is impossible: n = 5, ε = 1/15625, k = n³/ε, u₁ = u₂ = 0, u₃ = u₄ = (1,…,1), u₅ = (1, .99, .98, .97, .96) gives 468 748 interpolating agents vs 390 625 awesome goods; n = 3, ε = 100, k = 3, u₁ = u₃ = 0, u₂ = (1,1,1) gives 4 vs 1
--   - reading: dummies: "every agent has utility 2" for awesome goods (item 2) vs "identical utilities for all goods" (item 4) → every dummy values every good of G′, awesome goods included, at one common d ≥ 0, quantified over d; reason: the two printed items conflict for dummies; item 4 is the more specific
--   - reading: types t₁, …, tₙ ordered "in some arbitrary way"; chains between u_i and u_i′ (p.8) → types are the copy classes of the n original goods; the order and the direction of each pair's chain are free parameters, quantified over; the chain lists the vectors strictly between its ends after each ε-step, the last step possibly shorter; reason: the paper leaves these choices arbitrary; quantifying covers every choice
--   - generalization: rational utilities (p.2) → real utilities in [0,1]; reason: the count does not use rationality; it specializes to the rational case
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Lemma 12, p.8

import Mathlib
import Definitions.Def_CardinalMatching_ModParams

namespace CardinalMatching

/-- **Lemma 12** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, p.8): "Let n′ = |A′| = |G′| be the number of agents / goods in the
modified instance. Then n′ ≤ 2kn."

Stated as: under admissible parameters, the construction of `I′` balances (`|A′| = |G′|`, which
the paper's step 4 asserts) and `|G′| ≤ 2kn`.

**Formalization Note** `Admissible` carries correction C1 (`k ≥ n⁴/ε`, `k ≥ n⁴` in place of
`k ≥ n³/ε`); with the printed parameters the dummy agents of step 4 cannot balance the instance
(see `ModParams.Admissible`). -/
theorem lemma_12 {n : ℕ} (P : ModParams n) (hP : P.Admissible) :
    Fintype.card P.Agent = Fintype.card P.Good ∧ Fintype.card P.Good ≤ 2 * P.k * n := by sorry

end CardinalMatching
