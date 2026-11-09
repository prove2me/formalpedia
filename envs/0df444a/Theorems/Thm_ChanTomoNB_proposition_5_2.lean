-- Prove2me | Theorems.Thm_ChanTomoNB_proposition_5_2
-- name    : ChanTomoNB.proposition_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:30:28.782176+00:00
-- url     : https://prove2.me/theorems/57e8f8d9-b7ea-401b-96b9-fba6fc125edf
-- title:
--   Proposition 5.2 — $V_{P,U}$ is an isometry and $\mathcal E_{P,U}$ has Kraus rank exactly $r$
-- statement:
--   In the near-boundary regime ($d_2\ge2$, $r\ge1$, $d_1<rd_2<2d_1$), let $F$ be a balanced reference (Lemma 5.1) and $P\mapsto W_P$ a choice of isometries onto the projectors $P\in\mathrm{Proj}_{d'}(\operatorname{im}\Pi)$. For every such $P$ and every unitary $U\in\mathbb U(d')$:
--
--   1. $V_{P,U}=\begin{pmatrix}F&W_PU\end{pmatrix}$ is an isometry;
--   2. $\mathcal E_{P,U}=\operatorname{tr}_{\mathrm{anc}}\circ V_{P,U}$ lies in $\mathbf{QChan}^r_{d_1,d_2}$;
--   3. $\operatorname{rank}C_{\mathcal E_{P,U}}=r$.
--
--   So every member of the hard family is a valid instance of the tomography problem.
--
--   Differences from the source:
--   - encoding: standing assumptions of §5: d2 ≥ 2 (p.10, "throughout"), r ≥ 1 and d1 < rd2 < 2d1 (p.24, "This construction applies throughout the near-boundary regime") → explicit hypotheses 2 ≤ d2, 1 ≤ r, d1 < r·d2, r·d2 < 2·d1; reason: the result is stated under the section's standing assumptions
--   - generalization: "Fix such an isometry F", "fix an isometry W_P", "a fixed projector" (pp.25–26) → every isometry F with tr_B(FF†) ⪰ λ0 I_r, every choice P ↦ W_P with W_P†W_P = I and W_P W_P† = P, and (for µ) every isometry Ψ onto im Π; reason: the statement holds for every admissible choice and specializes to the paper's fixed ones
--   - encoding: "E_{P,U} is a channel with Kraus rank exactly r" → E_{P,U} ∈ QChan^r_{d1,d2} and rank C_{E_{P,U}} = r; reason: the Kraus rank is the rank of the Choi operator (p.10)
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, Proposition 5.2, p.26

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_ChanTomoNB_choiDist
import Definitions.Def_ChanTomoNB_diamondDist
import Definitions.Def_ChanTomoNB_matrixNorms
import Definitions.Def_ChanTomoNB_hardChannel

open Matrix MeasureTheory
open scoped ComplexOrder

namespace ChanTomoNB

/-- **Proposition 5.2 (Valid construction).** Chen, Oufkir, *Quantum channel tomography: optimal
bounds in the near-boundary regime*, arXiv:2611.03639v1, Proposition 5.2, p.26: "Every V_{P,U} in
Equation (50) is an isometry, and E_{P,U} is a channel with Kraus rank exactly r."

For every balanced reference `F` (Lemma 5.1), every choice `P ↦ W_P` of isometries onto the
rank-`d′` projectors `P ∈ Proj_{d′}(im Π)`, every such `P` and every unitary `U ∈ U(d′)`:
`V_{P,U} = [F  W_P U]` is an isometry, `E_{P,U} = tr_anc ∘ V_{P,U}` lies in `QChan^r_{d1,d2}`,
and its Choi operator has rank exactly `r`.

**Formalization Note.** "Kraus rank exactly r" is `rank C_{E_{P,U}} = r` together with
`E_{P,U} ∈ QChan^r` (p.10: the Kraus rank is the rank of the Choi operator). "Fix such an
isometry F" and "fix an isometry W_P" are read as universal quantification over every admissible
`F` and every choice `W` (Reading 7). -/
theorem proposition_5_2 (d1 d2 r : ℕ) (hd2 : 2 ≤ d2) (hr : 1 ≤ r) (hlo : d1 < r * d2)
    (hhi : r * d2 < 2 * d1)
    (F : Matrix (Fin d2 × Fin r) (Fin (d1 - dp d1)) ℂ) (hF : IsBalancedRef d1 d2 r F)
    (W : Matrix (Fin d2 × Fin r) (Fin d2 × Fin r) ℂ → Matrix (Fin d2 × Fin r) (Fin (dp d1)) ℂ)
    (hW : IsSignalChoice (d1 := d1) F W)
    (P : Matrix (Fin d2 × Fin r) (Fin d2 × Fin r) ℂ) (hP : P ∈ ProjIm (d1 := d1) F)
    (U : Matrix (Fin (dp d1)) (Fin (dp d1)) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin (dp d1)) ℂ) :
    (V5 (d1 := d1) F (W P) U)ᴴ * V5 (d1 := d1) F (W P) U = 1 ∧
      E5 (d1 := d1) F (W P) U ∈ QChan r d1 d2 ∧
      (choi (E5 (d1 := d1) F (W P) U)).rank = r := by sorry

end ChanTomoNB
