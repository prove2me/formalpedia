-- Prove2me | Theorems.Thm_BlottoFPTAS_Main_lemma_5_3
-- name    : BlottoFPTAS.Main.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:40:44.284499+00:00
-- url     : https://prove2.me/theorems/a6d20e11-68af-4bb9-86ed-07a4e49380f1
-- title:
--   Lemma 5.3 — the minimax equality C₁ + C_ρ = 1 for m ≥ 2 battlefields and ρ ∈ (0,1)
-- statement:
--   For $m\ge2$ battlefields, positive values $w$ summing to one and budgets $1$ and $\rho\in(0,1)$, let $C_1=\inf_PU_w(P;\rho)$ over strategies $P$ on $X(1)$ and $C_\rho=\inf_PU_w(P;1)$ over strategies $P$ on $X(\rho)$. Then
--   $$C_1+C_\rho=1.$$
--   No equilibrium is assumed: the existence theorems for discontinuous games cited in earlier work can fail here (App. C.1), and this equality is what lets the two players' strategies be computed separately.
--
--   Differences from the source:
--   - encoding: infimum over distributions on X(1), resp. X(ρ) → infimum over Borel probability measures with full mass on X(1), resp. X(ρ) (minSup); reason: Lean convention; the index set is nonempty and U is bounded below by 0
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 31, Lemma 5.3

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Game

namespace BlottoFPTAS.Main

/-- **Lemma 5.3** (Bichler, Ghosh, arXiv:2611.05221, held version sha256 cac3638e…, p. 31).
For `m ≥ 2` battlefields, positive values `w` summing to one and budgets `1` and `ρ ∈ (0, 1)`,
`C₁ + C_ρ = 1`, where `C₁ = inf_P U_w(P; ρ)` over strategies `P` on `X(1)` and
`C_ρ = inf_P U_w(P; 1)` over strategies `P` on `X(ρ)`. No equilibrium is assumed. -/
theorem lemma_5_3 {m : ℕ} (hm : 2 ≤ m) (w : Fin m → ℝ) (hw : ∀ j, 0 < w j)
    (hsum : ∑ j, w j = 1) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    minSup m w 1 ρ + minSup m w ρ 1 = 1 := by sorry

end BlottoFPTAS.Main
