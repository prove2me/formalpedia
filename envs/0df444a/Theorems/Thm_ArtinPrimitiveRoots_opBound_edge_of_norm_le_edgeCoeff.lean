-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_opBound_edge_of_norm_le_edgeCoeff
-- name    : ArtinPrimitiveRoots.opBound_edge_of_norm_le_edgeCoeff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T00:22:42.368082+00:00
-- url     : https://prove2.me/theorems/ddc835b0-e983-4c88-ba33-5092894ef9ac
-- title:
--   [21] (4.23)–(4.25) — an edge operation with coefficients dominated by those of E_j^ord has norm at most √R·√(3^K R), R the crude row bound
-- statement:
--   Let $P$ be any parameters, $\omega$ a root of the box, $j$ an edge index, and assume:
--   * $U, Y > 0$;
--   * $\nu_i(p) \ge 0$ on the group primes;
--   * $1/2 \le V_i \le 3/2$;
--   * $\sum_{p \in \mathcal P_i}\nu_i(p) \le 2$ for every group.
--
--   Let `cf` be coefficients with $|\mathrm{cf}(s, c)| \le |\texttt{edgeCoeff}\ \omega\ j\ s\ c|$.
--
--   Then the operator $f \mapsto \bigl(s \mapsto \sum_c \mathrm{cf}(s, c)\,f(\texttt{edgeOut}\ s\ c)\bigr)$, with outputs outside the state set dropped, has norm at most $\sqrt R\sqrt{3^KR}$ on $\ell^2(\texttt{stWeight})$. Here
--
--   $$R = 2^K\cdot 16\bigl(1 + (10Y + 1)\,|\mathfrak M|\bigr)(2 + 2B)^K$$
--
--   and $|\mathfrak M|$ is the measure of `majorArcs x A₀ Y`.
--
--   Source: [21] = OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), p. 24, (4.23)–(4.25).
-- source:
--   OpenAI, The Poisson-Dirichlet law for prime predecessors, OpenAI Math Release preprint, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf (Apache-2.0), p. 24, (4.23)–(4.25)

import Mathlib
import Definitions.Def_ArtinMarkedSquare
import Definitions.Def_ArtinMemoryModel

namespace ArtinPrimitiveRoots

open Finset MeasureTheory

theorem opBound_edge_of_norm_le_edgeCoeff (P : MemParams) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω)
    (hU : 0 < P.U) (hY : 0 < P.Y) (j : ℕ) (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p)
    (hV1 : ∀ i, 1 / 2 ≤ P.Vg i) (hV2 : ∀ i, P.Vg i ≤ 3 / 2)
    (hsum : ∀ i, ∑ p ∈ P.grp i, P.nu i p ≤ 2)
    (cf : P.MState → Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool) → ℂ)
    (hcf : ∀ s c, ‖cf s c‖ ≤ ‖P.edgeCoeff ω j s c‖) :
    P.OpBound (fun f s => ∑ c ∈ P.edgeChoices,
      cf s c * (if P.edgeOut s c ∈ P.stSet then f (P.edgeOut s c) else 0))
      (√(2 ^ P.K * (16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal)) *
          (2 + 2 * P.B) ^ P.K) *
        √(3 ^ P.K * (2 ^ P.K * (16 * (1 + (10 * P.Y + 1) *
          (volume (majorArcs P.x P.A₀ P.Y)).toReal)) * (2 + 2 * P.B) ^ P.K))) := by
  sorry

end ArtinPrimitiveRoots
