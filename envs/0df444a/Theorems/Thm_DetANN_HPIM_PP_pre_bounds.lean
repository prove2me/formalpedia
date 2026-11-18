-- Prove2me | Theorems.Thm_DetANN_HPIM_PP_pre_bounds
-- name    : DetANN.HPIM.PP.pre_bounds
-- status  : Proved
-- author  : @milia
-- created : 2026-11-17T09:26:56.583026+00:00
-- url     : https://prove2.me/theorems/0b00afd6-d404-46b4-b90f-0d646d4cf083
-- title:
--   Arithmetic of the preprocessing bounds
-- statement:
--   Let $m,N\ge1$, $\delta\in(0,1/2)$, let $\mathrm{ch}$ be child contracts with constants $C_m,C_c,C_b,C_{bal}$, and let $A=1+C_m+C_c+C_b+C_{bal}$. If $t_p\le4N(\lceil\log_2N\rceil+1)$, then, with the budget constants `KWc`, `KHc`, `KRc`, `WbIc`, `WbRc` (definition `DetANN_HPIMPreProg`):
--   $$79+4\lceil\log_2N\rceil+11N+5K_G+10T_{0G}+t_pK_W\le 256\cdot10^5A\,(N+m)^8\Bigl(\frac{2^{14}}\delta\Bigr)^{8m}\log^8\frac N\delta,$$
--   $$v_{0G}+18+D_n(W_I,N)+t_pK_H+t_pK_R+W_R\le 256\cdot10^5A\,N\Bigl(\frac{2^{14}}\delta\Bigr)^{8m}\log^8\frac N\delta.$$
--
--   With $t_p=\mathrm{treePts}$ (bounded by `tree_points`), these turn the exact work and cell counts of the driver into the bounds of `hpim_preprocessing`. The proof uses:
--   - Bernoulli: $(1+\delta/4)^{\lceil4/\delta\rceil}\ge2$, so $K_G=O(\log(N/\delta)/\delta)$;
--   - $\lceil(2^{14}/\delta)^{2m}\rceil\le2(2^{14}/\delta)^{2m}$;
--   - $\log2>1/2$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). These are the intermediate steps of the reduction of DetANN.HPIM.hpim_preprocessing, split so that each proof fits the verifier's time limit. The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_DetANN_HPIMPreProg
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMPreBlocks

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN DetANN.HPIM Classical

/-- **The arithmetic of the preprocessing bounds.** With `tp` points over the tree, the work and
cell budgets of the driver are within the bounds of `hpim_preprocessing`. -/
theorem pre_bounds {B : Blocks} (ch : ChildOK B) {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) (δ : ℝ)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2) (tp : ℕ) (htp0 : tp ≤ 4 * N * (Nat.clog 2 N + 1)) :
    ((79 + 4 * Nat.clog 2 N + 11 * N + 5 * KG N δ + 10 * T0G N δ + tp * KWc ch N m δ : ℕ) : ℝ) ≤
        ((256 * 100000 * Acon ch : ℕ) : ℝ) * ((N : ℝ) + m) ^ 8 *
          ((2 : ℝ) ^ 14 / δ) ^ (((8 : ℕ) : ℝ) * m) * Real.log (N / δ) ^ 8 ∧
      (((v0G N δ + 18 + Dn (WbIc ch N m δ) N + (tp : ℤ) * KHc ch N m δ + (tp : ℤ) * KRc ch N m δ +
          WbRc ch N m δ : ℤ)) : ℝ) ≤
        ((256 * 100000 * Acon ch : ℕ) : ℝ) * N *
          ((2 : ℝ) ^ 14 / δ) ^ (((8 : ℕ) : ℝ) * m) * Real.log (N / δ) ^ 8 := by sorry

end DetANN.HPIM.PP
