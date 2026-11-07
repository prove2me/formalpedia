-- Prove2me | Theorems.Thm_CompPermOracle_lemma_4_6
-- name    : CompPermOracle.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:49.138086+00:00
-- url     : https://prove2.me/theorems/8c8557f6-63a9-4132-8015-04660ec96ed8
-- title:
--   Lemma 4.6 — exact synthesis
-- statement:
--   Fix $x,y\in[N]$. For every $a\in K_r$,
--   $$
--   \sum_{j=r-1}^{r+1}E_jL_jM_{x,y}a=Q_{x,y}E_ra,
--   $$
--   where nonexistent levels are omitted. The identity compares a compressed query and a purified query after synthesis, with no error term on the frame range.
--
--   Differences from the source:
--   - encoding: nonexistent levels omitted → the sum over `Finset.Icc (r - 1) (r + 1)` with natural subtraction; $E_{N+1}=0$ as $\mathcal I_{N+1}$ is empty; reason: level $-1$ is left out at $r=0$, and the term at $N+1$ vanishes
--   - encoding: $[N]=\{1,\dots,N\}$, blank symbol $\bot$ → `Fin N` (0-based), $\bot$ = `none`; reason: a relabelling; no index appears in the bound
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Lemma 4.6, p.13

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels

namespace CompPermOracle

/-- Lemma 4.6, Exact synthesis (Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), p.13), eq. (17).

**Formalization Note.** "Nonexistent levels are omitted": the sum runs over `Finset.Icc (r - 1) (r + 1)`
with natural-number subtraction, so level `−1` is left out at `r = 0`, and `E_{N+1} = 0` since
`ℐ_{N+1}` is empty. The point `x` is fixed but arbitrary (§4.2). -/
theorem lemma_4_6 {N r : ℕ} (x y : Fin N) {a : Hil (PartialPerm N)} (ha : a ∈ Kr N r) :
    ∑ j ∈ Finset.Icc (r - 1) (r + 1), synth N j (Lproj N j (compM x y a)) =
      assertP x y (synth N r a) := by sorry

end CompPermOracle
