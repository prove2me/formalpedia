-- Prove2me | Theorems.Thm_ChanTomoNB_lemma_5_1
-- name    : ChanTomoNB.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:31:39.645507+00:00
-- url     : https://prove2.me/theorems/3b21eb37-1f12-4048-b57f-e468b6f10948
-- title:
--   Lemma 5.1 — balanced reference isometry $F$ with $\mathrm{tr}_B(FF^\dagger)\succeq\lambda_0I_r$
-- statement:
--   Let $d_2\ge2$, $r\ge1$ and $d_1<rd_2<2d_1$, and put $d'=\lfloor d_1/2\rfloor$ and $\lambda_0=(d_1-d')/(2r)$. There exists an isometry $F:\mathbb C^{d_1-d'}\to\mathbb C^{d_2}\otimes\mathbb C^{r}$ with
--   $$
--   \operatorname{tr}_B(FF^\dagger)\succeq\lambda_0I_r .
--   $$
--
--   The balanced reference spreads its image evenly over the ancilla, which makes every channel of the hard family have Kraus rank exactly $r$ and separates their Choi operators.
--
--   Differences from the source:
--   - encoding: standing assumptions of §5: d2 ≥ 2 (p.10, "throughout"), r ≥ 1 and d1 < rd2 < 2d1 (p.24, "This construction applies throughout the near-boundary regime") → explicit hypotheses 2 ≤ d2, 1 ≤ r, d1 < r·d2, r·d2 < 2·d1; reason: the result is stated under the section's standing assumptions
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, Lemma 5.1, p.25

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_ChanTomoNB_choiDist
import Definitions.Def_ChanTomoNB_diamondDist
import Definitions.Def_ChanTomoNB_matrixNorms
import Definitions.Def_ChanTomoNB_hardChannel

open Matrix MeasureTheory
open scoped ComplexOrder

namespace ChanTomoNB

/-- **Lemma 5.1 (Balanced reference).** Chen, Oufkir, *Quantum channel tomography: optimal
bounds in the near-boundary regime*, arXiv:2611.03639v1, Lemma 5.1, p.25: "There exists an
isometry F : H_{A1} → H_B ⊗ H_anc satisfying tr_B(FF†) ⪰ λ0 I_r, λ0 := (d − d′)/(2r)."

In the near-boundary regime `d1 < r d2 < 2 d1` with `d2 ≥ 2`, `r ≥ 1`, and with `d = d1`,
`d′ = ⌊d1/2⌋`, `H_{A1} = ℂ^{d1−d′}`, `H_B = ℂ^{d2}`, `H_anc = ℂ^r`, there is an isometry
`F : H_{A1} → H_B ⊗ H_anc` with `tr_B(F F†) ⪰ λ₀ I_r`.

**Formalization Note.** The hypotheses are the standing assumptions of §5 ("We take d2 ≥ 2
throughout", p.10; "This construction applies throughout the near-boundary regime
d1 < rd2 < 2d1", p.24). `IsBalancedRef` is `F†F = I` together with `tr_B(FF†) − λ₀ I ⪰ 0`. -/
theorem lemma_5_1 (d1 d2 r : ℕ) (hd2 : 2 ≤ d2) (hr : 1 ≤ r) (hlo : d1 < r * d2)
    (hhi : r * d2 < 2 * d1) :
    ∃ F : Matrix (Fin d2 × Fin r) (Fin (d1 - dp d1)) ℂ, IsBalancedRef d1 d2 r F := by sorry

end ChanTomoNB
