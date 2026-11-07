-- Prove2me | Theorems.Thm_CompPermOracle_lemma_4_11
-- name    : CompPermOracle.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:56:12.950195+00:00
-- url     : https://prove2.me/theorems/bcea242a-70eb-41f7-839b-b638ade40388
-- title:
--   Lemma 4.11 — the incidence maps control the distance to $K_j$
-- statement:
--   Let $1\le j\le N/2$ and $n=N-j$. Then on $\mathcal L_j$,
--   $$
--   \partial_j^\dagger\partial_j\succeq\frac{n-j+1}{n+1}(I-\Pi_{K_j}),
--   $$
--   with $\partial_j=(B^{\mathrm{dom}}_j,B^{\mathrm{im}}_j)$. Consequently, if $j\le(N+1)/3$, then for $b\in\mathcal L_j$,
--   $$
--   \|(I-\Pi_{K_j})b\|^2\le2\big(\|B^{\mathrm{dom}}_jb\|^2+\|B^{\mathrm{im}}_jb\|^2\big).
--   $$
--   So a vector nearly satisfying the zero-sum relations of $K_j$ is close to $K_j$: this is a quantitative converse of the zero-sum relations.
--
--   Differences from the source:
--   - reading: $\partial_j^\dagger\partial_j\succeq c(I-\Pi_{K_j})$ → for all $b\in\mathcal L_j$, $c\|(I-\Pi_{K_j})b\|^2\le\|B^{\mathrm{dom}}_jb\|^2+\|B^{\mathrm{im}}_jb\|^2$; reason: $\partial_j$ is a map on $\mathcal L_j$, and $I-\Pi_{K_j}$ is a projector, so this is the Loewner inequality
--   - encoding: $1\le j\le N/2$; $j\le(N+1)/3$ → `1 ≤ j`, `2 * j ≤ N`; `3 * j ≤ N + 1`; reason: with $1\le j$, the second implies the first, so the standing hypothesis needs no separate binder in (45)
--   - encoding: $[N]=\{1,\dots,N\}$, blank symbol $\bot$ → `Fin N` (0-based), $\bot$ = `none`; reason: a relabelling; no index appears in the bound
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Lemma 4.11, p.19

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels
import Definitions.Def_CompPermOracle_incidence

namespace CompPermOracle

/-- Lemma 4.11 (Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), p.19): eqs. (44) and (45), with `n = N − j`.

**Formalization Note.** `1 ≤ j ≤ N/2` is `1 ≤ j`, `2j ≤ N`. The Loewner inequality (44) is on `ℒ_j`,
where `∂_j` lives, and it is written as `⟨b, ∂_j†∂_j b⟩ = ‖B^dom_j b‖² + ‖B^im_j b‖² ≥ c‖(I − Π_{K_j})b‖²`,
which is the same since `I − Π_{K_j}` is a projector. In (45), `j ≤ (N + 1)/3` is `3j ≤ N + 1`; with
`1 ≤ j` it implies the standing `2j ≤ N`. -/
theorem lemma_4_11 {N j : ℕ} (hj : 1 ≤ j) :
    (2 * j ≤ N → ∀ b ∈ Lsub N j,
      (((N : ℝ) - j - j + 1) / ((N : ℝ) - j + 1)) * ‖b - ProjK N j b‖ ^ 2 ≤
        ‖Bdom N j b‖ ^ 2 + ‖Bim N j b‖ ^ 2) ∧
    (3 * j ≤ N + 1 → ∀ b ∈ Lsub N j,
      ‖b - ProjK N j b‖ ^ 2 ≤ 2 * (‖Bdom N j b‖ ^ 2 + ‖Bim N j b‖ ^ 2)) := by sorry

end CompPermOracle
