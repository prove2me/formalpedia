-- Prove2me | Theorems.Thm_CompPermOracle_lemma_4_14
-- name    : CompPermOracle.lemma_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:27.251215+00:00
-- url     : https://prove2.me/theorems/9fd4d1bd-0ca0-4c03-aa74-a25593dac68e
-- title:
--   Lemma 4.14 — the middle block of a compressed query on $K_r$
-- statement:
--   Fix $x,y\in[N]$, $m=N-r$. For $a,c\in K_r$,
--   $$
--   \langle c,L_rM_{x,y}L_ra\rangle=\Big\langle c,\Big(\frac1mR^{00}_{x,y;r}+R^{11}_{x,y;r}\Big)a\Big\rangle.
--   $$
--   Consequently,
--   $$
--   h^0_{y,r}=V_r\big(H^{00}_{y,r}+H^{11}_{y,r}-A_{y,r}G_r\big)G_r^{-1}=V_r\big(H^{00}_{y,r}G_r^{-1}+H^{11}_{y,r}G_r^{-1}-A_{y,r}\big).
--   $$
--   This reduces the bound on $h^0$ to a comparison of the true assertion with fixed-edge frames.
--
--   Differences from the source:
--   - encoding: $h^0_{y,r}$ on $\mathcal H_r$, $G_r^{-1}$ → $h^0_{y,r}$ precomposed with $\Pi_r$, and the inverse on $\mathcal H_r$ extended by $0$; reason: (70) then holds as an identity of operators on $\mathcal P$, as every term vanishes off $\mathcal H_r$
--   - encoding: $[N]=\{1,\dots,N\}$, blank symbol $\bot$ → `Fin N` (0-based), $\bot$ = `none`; reason: a relabelling; no index appears in the bound
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Lemma 4.14, p.23

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels
import Definitions.Def_CompPermOracle_oneQuery

namespace CompPermOracle

/-- Lemma 4.14 (Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), p.23): eq. (69) and the two forms of eq. (70), with `m = N − r`.

**Formalization Note.** `G_r^{−1}` is the inverse on `ℋ_r` extended by `0` (`GramInv`). `h⁰_{y,r}` is
precomposed with `Π_r`, so (70) holds as an identity of operators on `𝒫`: every term vanishes off `ℋ_r`. -/
theorem lemma_4_14 {N r : ℕ} (x y : Fin N) :
    (∀ a ∈ Kr N r, ∀ c ∈ Kr N r,
      inner ℂ c (Lproj N r (compM x y (Lproj N r a))) =
        inner ℂ c (((((((N : ℝ) - r)⁻¹ : ℝ) : ℂ) • selR00 x y r) + selR11 x y r) a)) ∧
    hZero x y r =
      (Vr N r).comp
        ((opH00 x y r + opH11 x y r - (opA x y r).comp (Gram N r)).comp (GramInv N r)) ∧
    hZero x y r =
      (Vr N r).comp
        ((opH00 x y r).comp (GramInv N r) + (opH11 x y r).comp (GramInv N r) - opA x y r) := by sorry

end CompPermOracle
