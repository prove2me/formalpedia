-- Prove2me | Theorems.Thm_ChanTomoNB_lemma_5_8
-- name    : ChanTomoNB.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:30:45.424843+00:00
-- url     : https://prove2.me/theorems/685a55c2-9a48-4d52-9783-b3a861d9d48c
-- title:
--   Lemma 5.8 — Choi separation $d_1^{-1}\|C_{\mathcal E_{P,U}}-C_{\mathcal E_{Q,U'}}\|_1\ge d_1^{-1}\sqrt{\lambda_0/\kappa}\,\|P-Q\|_1$
-- statement:
--   In the near-boundary regime ($d_2\ge2$, $r\ge1$, $d_1<rd_2<2d_1$), let $F$ be a balanced reference and $P\mapsto W_P$ a choice of isometries. For $P\in\mathcal G$, $Q\in\mathrm{Proj}_{d'}(\operatorname{im}\Pi)$ and $U,U'\in\mathbb U(d')$,
--   $$
--   \frac1{d_1}\|C_{\mathcal E_{P,U}}-C_{\mathcal E_{Q,U'}}\|_1\ge\frac1{d_1}\sqrt{\frac{\lambda_0}{\kappa}}\,\|P-Q\|_1 .
--   $$
--
--   Distinct signal ranges give channels that are far apart in Choi trace norm, whatever the masks.
--
--   Differences from the source:
--   - encoding: standing assumptions of §5: d2 ≥ 2 (p.10, "throughout"), r ≥ 1 and d1 < rd2 < 2d1 (p.24, "This construction applies throughout the near-boundary regime") → explicit hypotheses 2 ≤ d2, 1 ≤ r, d1 < r·d2, r·d2 < 2·d1; reason: the result is stated under the section's standing assumptions
--   - generalization: "Fix such an isometry F", "fix an isometry W_P", "a fixed projector" (pp.25–26) → every isometry F with tr_B(FF†) ⪰ λ0 I_r, every choice P ↦ W_P with W_P†W_P = I and W_P W_P† = P, and (for µ) every isometry Ψ onto im Π; reason: the statement holds for every admissible choice and specializes to the paper's fixed ones
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, Lemma 5.8, Eq. (61), p.29

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_ChanTomoNB_choiDist
import Definitions.Def_ChanTomoNB_diamondDist
import Definitions.Def_ChanTomoNB_matrixNorms
import Definitions.Def_ChanTomoNB_hardChannel

open Matrix MeasureTheory
open scoped ComplexOrder

namespace ChanTomoNB

/-- **Lemma 5.8 (Choi separation).** Chen, Oufkir, *Quantum channel tomography: optimal bounds in
the near-boundary regime*, arXiv:2611.03639v1, Lemma 5.8, Eq. (61), p.29: "Let P ∈ G,
Q ∈ Proj_{d′}(imΠ) and U, U′ ∈ U(d′). We have that
(1/d1)‖C_{E_{P,U}} − C_{E_{Q,U′}}‖_1 ≥ (1/d1)√(λ0/κ) ‖P − Q‖_1."

**Formalization Note.** The left side is `choiDist`; `G` is `goodSet F`; `λ₀ = (d1 − d′)/(2r)`,
`κ = 450(α/r + 1/d2)` in `ℝ`. The balanced reference `F` and the choice `W` are arbitrary
admissible ones (Reading 7). -/
theorem lemma_5_8 (d1 d2 r : ℕ) (hd2 : 2 ≤ d2) (hr : 1 ≤ r) (hlo : d1 < r * d2)
    (hhi : r * d2 < 2 * d1)
    (F : Matrix (Fin d2 × Fin r) (Fin (d1 - dp d1)) ℂ) (hF : IsBalancedRef d1 d2 r F)
    (W : Matrix (Fin d2 × Fin r) (Fin d2 × Fin r) ℂ → Matrix (Fin d2 × Fin r) (Fin (dp d1)) ℂ)
    (hW : IsSignalChoice (d1 := d1) F W)
    (P Q : Matrix (Fin d2 × Fin r) (Fin d2 × Fin r) ℂ)
    (hP : P ∈ goodSet (d1 := d1) F) (hQ : Q ∈ ProjIm (d1 := d1) F)
    (U U' : Matrix (Fin (dp d1)) (Fin (dp d1)) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin (dp d1)) ℂ)
    (hU' : U' ∈ Matrix.unitaryGroup (Fin (dp d1)) ℂ) :
    1 / (d1 : ℝ) * Real.sqrt (lam0 d1 r / kappa d1 d2 r) * WildeQIT.traceNorm (P - Q) ≤
      choiDist (E5 (d1 := d1) F (W P) U) (E5 (d1 := d1) F (W Q) U') := by sorry

end ChanTomoNB
