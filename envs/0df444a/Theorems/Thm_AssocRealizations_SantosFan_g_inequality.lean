-- Prove2me | Theorems.Thm_AssocRealizations_SantosFan_g_inequality
-- name    : AssocRealizations.SantosFan.g_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:39.809982+00:00
-- url     : https://prove2.me/theorems/ee91dba7-91dc-4eb9-9800-0a23d5a74b4f
-- title:
--   p. 23 — $g_{ij} = (j-i)(n+3+i-j)$ satisfies $g_{ik}+g_{jl} > \max\{g_{ij}+g_{kl},\, g_{il}+g_{jk}\}$
-- statement:
--   For $n \ge 0$ and integers $i, j$ put $g_{ij} = (j - i)(n + 3 + i - j)$. Then for all integers $1 \le i < j < k < l \le n+3$,
--   $$g_{ik} + g_{jl} > \max\{\, g_{ij} + g_{kl},\ g_{il} + g_{jk} \,\}.$$
--
--   Read on the $(n+3)$-gon with vertices $1, \dots, n+3$, $g_{ij}$ is a weight on chords, and the inequality says that for every quadrilateral $ijkl$ the two crossing diagonals $ik, jl$ have larger total weight than either pair of opposite sides. It is the perturbation that makes Santos' fan polytopal in the degenerate case (4) of Lemma 5.3.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 23, proof of Theorem 5.2

import Mathlib
import Definitions.Def_AssocRealizations_SantosFan_Setting

namespace AssocRealizations.SantosFan

open ChvatalArtGallery.FanPartition

/-- The inequality of p. 23: `g_ij = (j - i)(n + 3 + i - j)` satisfies
`g_ik + g_jl > max {g_ij + g_kl, g_il + g_jk}` for all `1 ≤ i < j < k < l ≤ n + 3`. -/
theorem g_inequality (n : ℕ) (i j k l : ℤ) (hi : 1 ≤ i) (hij : i < j) (hjk : j < k)
    (hkl : k < l) (hl : l ≤ (n : ℤ) + 3) :
    max (gW n i j + gW n k l) (gW n i l + gW n j k) < gW n i k + gW n j l := by sorry

end AssocRealizations.SantosFan
