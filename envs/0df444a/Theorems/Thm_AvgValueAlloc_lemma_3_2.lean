-- Prove2me | Theorems.Thm_AvgValueAlloc_lemma_3_2
-- name    : AvgValueAlloc.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:24.183338+00:00
-- url     : https://prove2.me/theorems/067e4e31-0db5-43d6-acd8-78ae775b564c
-- title:
--   Lemma 3.2 — Balanced validation
-- statement:
--   Let $\rho\in\mathbb Q^n_{>0}$, $M$ fixed ordered funding items with ambiguity at most $\sigma$, and $U$ an unordered union of $2r$ records split into uniform complementary halves $Y$ and $Z$. With $h=1+\log(\sigma+1)$, every selected bank $B_g=B(X)$, $X$ a routing of $M$ chosen from the split, satisfies
--   $$
--   \mathbb E\,G_Y(B_g)\ \le\ 4\,\mathbb E\,G_Z(B_g)+64\,h\,P(M).
--   $$
--   This replaces independence by exchangeability in the random-order analysis.
--
--   Differences from the source:
--   - generalization: h = 1 + log(σ_Q + 1) → h = 1 + log(σ + 1) for every σ ≥ σ_M; reason: M is part of the live multiset Q, so σ_Q ≥ σ_M is one such σ
--   - generalization: a bank selected from the information half → a routing selected by any function of the split; reason: the proof bounds every bank simultaneously; selection from Y is a special case
--   - encoding: uniform complementary halves → a uniform r-subset S of the 2r indices, Y = U|_S, Z = U|_{S^c}; reason: same law
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §3.2, Lemma 3.2, p.8

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_sigmaOn
import Definitions.Def_AvgValueAlloc_posVal
import Definitions.Def_AvgValueAlloc_routBank
import Definitions.Def_AvgValueAlloc_groupSum
import Definitions.Def_AvgValueAlloc_restrictTo

namespace AvgValueAlloc

/-- **Lemma 3.2 (Balanced validation).**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §3.2, Lemma 3.2, p.8: "With h = 1 + log(σ_Q + 1),
EG_Y(B_g) ≤ 4EG_Z(B_g) + 64hP(M) for every selected bank." Setting, p.8: "condition on ordered M,
unordered 2r-record union U = Y ⊎ Z, and leftovers. The two lists are uniform complementary halves,
not independent samples."

Let `ρ > 0`, `M` fixed funding items, `σ ≥ σ_M`, and `U` a list of `2r` records. Let `Y` be the
records of a uniform `r`-subset `S` of `U` and `Z` the other `r`. For every rule selecting a
routing `X` of `M` from `S`, with `B_g = B(X)` and `h = 1 + log(σ + 1)`:
`E G_Y(B_g) ≤ 4 E G_Z(B_g) + 64 h P(M)`.

**Formalization Note.** `σ` is any upper bound on the ambiguity of `M`; the page's `σ_Q` (the
live multiset contains `M`) is one. The selection may read the whole split. -/
theorem lemma_3_2 {n m : ℕ} (ρ : Fin n → ℚ) (hρ : ∀ j, 0 < ρ j) (M : Fin m → Vec n) (σ : ℕ)
    (hσ : sigmaOn ρ (Finset.univ.image M) ≤ σ) (r : ℕ) (U : Fin (2 * r) → Vec n)
    (sel : Finset (Fin (2 * r)) → Fin m → Option (Fin n)) (hsel : ∀ S, IsRouting ρ M (sel S)) :
    (∑ S ∈ (Finset.univ : Finset (Fin (2 * r))).powersetCard r,
        Gdy ρ (restrictTo U S) (routBank ρ M (sel S))) / ((2 * r).choose r : ℝ) ≤
      4 * ((∑ S ∈ (Finset.univ : Finset (Fin (2 * r))).powersetCard r,
          Gdy ρ (restrictTo U Sᶜ) (routBank ρ M (sel S))) / ((2 * r).choose r : ℝ)) +
        64 * (1 + Real.log ((σ : ℝ) + 1)) * posValSum ρ M := by sorry

end AvgValueAlloc
