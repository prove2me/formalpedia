-- Prove2me | Theorems.Thm_ChanTomoNB_lemma_5_14
-- name    : ChanTomoNB.lemma_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:30:41.859288+00:00
-- url     : https://prove2.me/theorems/613f3ef3-28da-4d1b-be34-22272a419f97
-- title:
--   Lemma 5.14 — Haar small balls: $\mu\{Q:\|P-Q\|_1\le s\}\le\min\{1,(e(d'+\alpha)s/(4\alpha d'))^{2\alpha d'}\}$
-- statement:
--   In the near-boundary regime ($d_2\ge2$, $r\ge1$, $d_1<rd_2<2d_1$), let $F$ be a balanced reference and $\mu$ the invariant probability measure on $\mathrm{Proj}_{d'}(\operatorname{im}\Pi)$. For every $P\in\mathrm{Proj}_{d'}(\operatorname{im}\Pi)$ and every $s\ge0$,
--   $$
--   \mu\{Q:\|P-Q\|_1\le s\}\le\min\Big\{1,\Big(\frac{e(d'+\alpha)s}{4\alpha d'}\Big)^{2\alpha d'}\Big\}.
--   $$
--
--   Small balls have small measure, so a maximal packing of $\mathcal G$ is large.
--
--   Differences from the source:
--   - encoding: standing assumptions of §5: d2 ≥ 2 (p.10, "throughout"), r ≥ 1 and d1 < rd2 < 2d1 (p.24, "This construction applies throughout the near-boundary regime") → explicit hypotheses 2 ≤ d2, 1 ≤ r, d1 < r·d2, r·d2 < 2·d1; reason: the result is stated under the section's standing assumptions
--   - generalization: "Fix such an isometry F", "fix an isometry W_P", "a fixed projector" (pp.25–26) → every isometry F with tr_B(FF†) ⪰ λ0 I_r, every choice P ↦ W_P with W_P†W_P = I and W_P W_P† = P, and (for µ) every isometry Ψ onto im Π; reason: the statement holds for every admissible choice and specializes to the paper's fixed ones
--   - encoding: µ, the invariant probability measure on Proj_{d′}(im Π), obtained by conjugating a fixed projector by a Haar unitary (p.26) → µ(S) = Haar probability of {U ∈ U(d′+α) : Ψ U P0 U† Ψ† ∈ S}, P0 = diag(I_{d′}, 0_α); reason: the pushforward law, evaluated on the closed sets used here
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, Lemma 5.14, p.32

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_ChanTomoNB_choiDist
import Definitions.Def_ChanTomoNB_diamondDist
import Definitions.Def_ChanTomoNB_matrixNorms
import Definitions.Def_ChanTomoNB_hardChannel

open Matrix MeasureTheory
open scoped ComplexOrder

namespace ChanTomoNB

/-- **Lemma 5.14 (Haar small balls).** Chen, Oufkir, *Quantum channel tomography: optimal bounds
in the near-boundary regime*, arXiv:2611.03639v1, Lemma 5.14, p.32: "For every P ∈ Proj_{d′}(imΠ)
and s ≥ 0, µ{Q : ‖P − Q‖_1 ≤ s} ≤ min{1, (e(d′ + α)s/(4αd′))^{2αd′}}."

In the near-boundary regime, for every balanced reference `F`, every isometry `Ψ` onto `im Π`
(defining `µ`), every `P ∈ Proj_{d′}(im Π)` and every `s ≥ 0`,
`µ{Q : ‖P − Q‖₁ ≤ s} ≤ min{1, (e(d′+α)s/(4αd′))^{2αd′}}`.

**Formalization Note.** `‖·‖₁` is `WildeQIT.traceNorm`; `µ` is `muProj Ψ` (Reading 7); the
bound is a real number mapped into `ℝ≥0∞` by `ENNReal.ofReal` (it is nonnegative). -/
theorem lemma_5_14 (d1 d2 r : ℕ) (hd2 : 2 ≤ d2) (hr : 1 ≤ r) (hlo : d1 < r * d2)
    (hhi : r * d2 < 2 * d1)
    (F : Matrix (Fin d2 × Fin r) (Fin (d1 - dp d1)) ℂ) (hF : IsBalancedRef d1 d2 r F)
    (Ψ : Matrix (Fin d2 × Fin r) (Fin (dp d1 + alpha d1 d2 r)) ℂ) (hΨ : IsOuterIsometry (d1 := d1) F Ψ)
    (P : Matrix (Fin d2 × Fin r) (Fin d2 × Fin r) ℂ) (hP : P ∈ ProjIm (d1 := d1) F)
    (s : ℝ) (hs : 0 ≤ s) :
    muProj (d1 := d1) Ψ {Q | WildeQIT.traceNorm (P - Q) ≤ s} ≤
      ENNReal.ofReal (min 1 ((Real.exp 1 * ((dp d1 : ℝ) + alpha d1 d2 r) * s /
        (4 * (alpha d1 d2 r : ℝ) * dp d1)) ^ (2 * alpha d1 d2 r * dp d1))) := by sorry

end ChanTomoNB
