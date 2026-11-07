-- Prove2me | Theorems.Thm_CompPermOracle_theorem_4_2
-- name    : CompPermOracle.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:55.120868+00:00
-- url     : https://prove2.me/theorems/6c47d133-6f78-48f3-b281-67f35ea188b5
-- title:
--   Theorem 4.2 — intertwiner and soundness
-- statement:
--   Let $N\ge3$. The map $\tilde V:\mathcal P\to\mathcal L$ is a degree-preserving isometry, in the sense that $\tilde V$ maps $\mathcal H_r$ to a subspace of $\mathcal L_r$, and $\tilde V|S_N\rangle=|\emptyset\rangle$. For every $x\in[N]$ and every integer $t\ge0$ with $3t+2\le N$,
--   $$
--   \big\|\big(\mathrm{cpO}_x(I_{\mathcal A}\otimes V)-(I_{\mathcal A}\otimes V)P_x\big)(I_{\mathcal A}\otimes\Pi_{\le t})\big\|\le\frac{60}{\sqrt{N-t}},
--   $$
--   $$
--   \big\|\big(\mathrm{cpO}_x(I_{\mathcal A}\otimes\tilde V)-(I_{\mathcal A}\otimes\tilde V)P_x\big)(I_{\mathcal A}\otimes\Pi_{\le t})\big\|\le\frac{60}{\sqrt{N-t}}+\frac{t+1}{N-2t-1}.
--   $$
--   The same bounds hold for the inverse queries $\mathrm{cpO}^{-1}_y$ against $P^{-1}_y$, and for the coherently controlled operators $\mathrm{cpO}$ against $P$ and $\mathrm{cpO}^{-1}$ against $P^{-1}$.
--
--   This is the one-query engine behind the soundness of the compressed permutation oracle.
--
--   Differences from the source:
--   - reading: isometry; the same bounds for inverse queries and for coherently controlled operators → norm preservation on $\mathcal P$; four explicit bounds with the input register added for the controlled operators; reason: the coherently controlled operators are named on pp.6 and 8
--   - encoding: $[N]=\{1,\dots,N\}$, blank symbol $\bot$ → `Fin N` (0-based), $\bot$ = `none`; reason: a relabelling; no index appears in the bound
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Theorem 4.2, p.12

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels
import Definitions.Def_CompPermOracle_oneQuery

namespace CompPermOracle

/-- Theorem 4.2, Intertwiner and soundness (Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), p.12): `Ṽ` is a degree-preserving
isometry, (10), (11), (12), and the same bounds for the inverse queries and for the coherently
controlled forward and inverse query operators.

**Formalization Note.** "Isometry" is norm preservation on `𝒫`. `cpO⁻¹_y` is compared with `P⁻¹_y`
for every `y`, and the controlled operators are `cpO` against `P` and `cpO⁻¹` against `P⁻¹`, with the
input register added. -/
theorem theorem_4_2 {N : ℕ} (hN : 3 ≤ N) :
    (∀ ψ, ‖Vtmap N ψ‖ = ‖ψ‖) ∧
    (∀ r, ∀ ψ ∈ Hlevel N r, Vtmap N ψ ∈ Lsub N r) ∧
    Vtmap N (uniformPerm N) = ket ⊥ ∧
    ∀ t : ℕ, 3 * t + 2 ≤ N →
      (∀ x : Fin N,
        ‖queryErr (Vmap N) (cpOAt x) (purP x) t‖ ≤ 60 / Real.sqrt ((N : ℝ) - t) ∧
        ‖queryErr (Vtmap N) (cpOAt x) (purP x) t‖ ≤
          60 / Real.sqrt ((N : ℝ) - t) + ((t : ℝ) + 1) / ((N : ℝ) - 2 * t - 1) ∧
        ‖queryErr (Vmap N) (cpOInvAt x) (purPInv x) t‖ ≤ 60 / Real.sqrt ((N : ℝ) - t) ∧
        ‖queryErr (Vtmap N) (cpOInvAt x) (purPInv x) t‖ ≤
          60 / Real.sqrt ((N : ℝ) - t) + ((t : ℝ) + 1) / ((N : ℝ) - 2 * t - 1)) ∧
      ‖queryErrCtl (Vmap N) cpOCtl purPCtl t‖ ≤ 60 / Real.sqrt ((N : ℝ) - t) ∧
      ‖queryErrCtl (Vtmap N) cpOCtl purPCtl t‖ ≤
        60 / Real.sqrt ((N : ℝ) - t) + ((t : ℝ) + 1) / ((N : ℝ) - 2 * t - 1) ∧
      ‖queryErrCtl (Vmap N) cpOInvCtl purPInvCtl t‖ ≤ 60 / Real.sqrt ((N : ℝ) - t) ∧
      ‖queryErrCtl (Vtmap N) cpOInvCtl purPInvCtl t‖ ≤
        60 / Real.sqrt ((N : ℝ) - t) + ((t : ℝ) + 1) / ((N : ℝ) - 2 * t - 1) := by sorry

end CompPermOracle
