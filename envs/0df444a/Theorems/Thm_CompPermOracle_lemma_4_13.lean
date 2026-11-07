-- Prove2me | Theorems.Thm_CompPermOracle_lemma_4_13
-- name    : CompPermOracle.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:56:03.177385+00:00
-- url     : https://prove2.me/theorems/4a3a0564-b66f-46e3-b14e-c423c519a2f7
-- title:
--   Lemma 4.13 — square-function bounds for the stacked incidence terms
-- statement:
--   Assume $r\le m$, where $m=N-r$. Fix $x\in[N]$, and let $\Theta_{y,r}a=(B^{\mathrm{im}}_{r+1}b^+_y,B^{\mathrm{dom}}_{r+1}b^+_y,B^{\mathrm{im}}_rb^0_y,B^{\mathrm{dom}}_rb^0_y)$, where $b^+_y=L_{r+1}M_ya$ and $b^0_y=L_rM_ya$. Then, as operators on $K_r$,
--   $$
--   \mathrm{Col}(\Theta_{\cdot,r})^2\le\frac8m,\qquad\mathrm{Row}(\Theta_{\cdot,r})^2\le\frac{22}{m}.
--   $$
--   Together with the previous bounds, this gives the leakage estimate out of the frame ranges.
--
--   Differences from the source:
--   - reading: as operators on $K_r$ → the family precomposed with $\Pi_{K_r}$; reason: a family on $K_r$ and its extension by $0$ have the same $\mathrm{Col}$ and $\mathrm{Row}$
--   - encoding: the 4-tuple, into $\bigoplus\mathbb C|h,b\rangle$ → a map into $\mathcal H(\mathrm{Fin}\ 4\times\mathcal I\times[N])$; reason: an isometric inclusion
--   - encoding: $[N]=\{1,\dots,N\}$, blank symbol $\bot$ → `Fin N` (0-based), $\bot$ = `none`; reason: a relabelling; no index appears in the bound
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Lemma 4.13, p.20

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels
import Definitions.Def_CompPermOracle_incidence

namespace CompPermOracle

/-- Lemma 4.13 (Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), p.20), eq. (52), with `m = N − r`.

**Formalization Note.** `Theta` is precomposed with `Π_{K_r}`, which expresses "as operators on `K_r`";
`Col` and `Row` are the same for the family on `K_r` and for its extension by `0`. `B^•_0 = 0` at
`r = 0`. -/
theorem lemma_4_13 {N r : ℕ} (hr : (r : ℝ) ≤ (N : ℝ) - r) (x : Fin N) :
    Col (fun y => Theta x y r) ^ 2 ≤ 8 / ((N : ℝ) - r) ∧
    Row (fun y => Theta x y r) ^ 2 ≤ 22 / ((N : ℝ) - r) := by sorry

end CompPermOracle
