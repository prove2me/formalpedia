-- Prove2me | Theorems.Thm_ChanTomoNB_lemma_5_7
-- name    : ChanTomoNB.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:30:51.851517+00:00
-- url     : https://prove2.me/theorems/1561cd98-ab93-4191-9892-87620585c433
-- title:
--   Lemma 5.7 — range displacement: $\Delta_{\mathrm{out}}=[0\ \ N_PN_P^\dagger W_QU']$ and its three norms
-- statement:
--   In the near-boundary regime ($d_2\ge2$, $r\ge1$, $d_1<rd_2<2d_1$), let $F$ be a balanced reference and $P\mapsto W_P$ a choice of isometries. Let $P,Q\in\mathrm{Proj}_{d'}(\operatorname{im}\Pi)$, $U,U'\in\mathbb U(d')$, $V=V_{P,U}$, $\hat V=V_{Q,U'}$ and
--   $$
--   \Delta_{\mathrm{out}}=(I-VV^\dagger)\hat V .
--   $$
--   Let $N_P:\mathbb C^\alpha\to\operatorname{im}\Pi$ be an isometry with $N_PN_P^\dagger=\Pi-P$. Then
--   $$
--   \Delta_{\mathrm{out}}=\begin{pmatrix}0&N_PN_P^\dagger W_QU'\end{pmatrix},\quad \|\Delta_{\mathrm{out}}\|_1=\tfrac12\|P-Q\|_1,\quad \|\Delta_{\mathrm{out}}\|_{\mathrm{op}}=\|P-Q\|_{\mathrm{op}},\quad \|\Delta_{\mathrm{out}}\|_F^2=\tfrac12\|P-Q\|_F^2,
--   $$
--   and $\operatorname{rank}(P-Q)\le2\min\{\alpha,d'\}$.
--
--   The part of $\hat V$ outside the range of $V$ is controlled by the distance between the signal ranges, uniformly in the Haar masks.
--
--   Differences from the source:
--   - encoding: standing assumptions of §5: d2 ≥ 2 (p.10, "throughout"), r ≥ 1 and d1 < rd2 < 2d1 (p.24, "This construction applies throughout the near-boundary regime") → explicit hypotheses 2 ≤ d2, 1 ≤ r, d1 < r·d2, r·d2 < 2·d1; reason: the result is stated under the section's standing assumptions
--   - generalization: "Fix such an isometry F", "fix an isometry W_P", "a fixed projector" (pp.25–26) → every isometry F with tr_B(FF†) ⪰ λ0 I_r, every choice P ↦ W_P with W_P†W_P = I and W_P W_P† = P, and (for µ) every isometry Ψ onto im Π; reason: the statement holds for every admissible choice and specializes to the paper's fixed ones
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, Lemma 5.7, Eq. (60), p.29

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_ChanTomoNB_choiDist
import Definitions.Def_ChanTomoNB_diamondDist
import Definitions.Def_ChanTomoNB_matrixNorms
import Definitions.Def_ChanTomoNB_hardChannel

open Matrix MeasureTheory
open scoped ComplexOrder

namespace ChanTomoNB

/-- **Lemma 5.7 (Range displacement).** Chen, Oufkir, *Quantum channel tomography: optimal bounds
in the near-boundary regime*, arXiv:2611.03639v1, Lemma 5.7, Eq. (60), p.29: "For P, Q, U, U′ and
∆_out as above, let N_P : C^α → im Π be an isometry with N_P N_P† = Π − P. Then
∆_out = [ 0  N_P N_P† W_Q U′ ], ‖∆_out‖_1 = (1/2)‖P − Q‖_1, ‖∆_out‖_op = ‖P − Q‖_op,
‖∆_out‖_F² = (1/2)‖P − Q‖_F². Moreover, rank(P − Q) ≤ 2 min{α, d′}."

Here `V = V_{P,U}`, `V̂ = V_{Q,U′}` and `∆_out = (I − V V†) V̂` (p.29, "We use the same
perturbation notation").

**Formalization Note.** `‖·‖₁` is `WildeQIT.traceNorm`, `‖·‖_op` is `opNorm`, `‖·‖_F` is
`frobNorm`. `[0  X]` is `Matrix.fromCols 0 X` on the input `ℂ^{d1−d′} ⊕ ℂ^{d′}`. The balanced
reference `F` and the choice `W` are arbitrary admissible ones (Reading 7). -/
theorem lemma_5_7 (d1 d2 r : ℕ) (hd2 : 2 ≤ d2) (hr : 1 ≤ r) (hlo : d1 < r * d2)
    (hhi : r * d2 < 2 * d1)
    (F : Matrix (Fin d2 × Fin r) (Fin (d1 - dp d1)) ℂ) (hF : IsBalancedRef d1 d2 r F)
    (W : Matrix (Fin d2 × Fin r) (Fin d2 × Fin r) ℂ → Matrix (Fin d2 × Fin r) (Fin (dp d1)) ℂ)
    (hW : IsSignalChoice (d1 := d1) F W)
    (P Q : Matrix (Fin d2 × Fin r) (Fin d2 × Fin r) ℂ)
    (hP : P ∈ ProjIm (d1 := d1) F) (hQ : Q ∈ ProjIm (d1 := d1) F)
    (U U' : Matrix (Fin (dp d1)) (Fin (dp d1)) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin (dp d1)) ℂ)
    (hU' : U' ∈ Matrix.unitaryGroup (Fin (dp d1)) ℂ)
    (NP : Matrix (Fin d2 × Fin r) (Fin (alpha d1 d2 r)) ℂ) (hN1 : NPᴴ * NP = 1)
    (hN2 : NP * NPᴴ = PiF (d1 := d1) F - P) :
    (1 - V5 (d1 := d1) F (W P) U * (V5 (d1 := d1) F (W P) U)ᴴ) * V5 (d1 := d1) F (W Q) U' =
        Matrix.fromCols 0 (NP * NPᴴ * W Q * U') ∧
      WildeQIT.traceNorm ((1 - V5 (d1 := d1) F (W P) U * (V5 (d1 := d1) F (W P) U)ᴴ) *
        V5 (d1 := d1) F (W Q) U') = 1 / 2 * WildeQIT.traceNorm (P - Q) ∧
      opNorm ((1 - V5 (d1 := d1) F (W P) U * (V5 (d1 := d1) F (W P) U)ᴴ) *
        V5 (d1 := d1) F (W Q) U') = opNorm (P - Q) ∧
      frobNorm ((1 - V5 (d1 := d1) F (W P) U * (V5 (d1 := d1) F (W P) U)ᴴ) *
        V5 (d1 := d1) F (W Q) U') ^ 2 = 1 / 2 * frobNorm (P - Q) ^ 2 ∧
      (P - Q).rank ≤ 2 * min (alpha d1 d2 r) (dp d1) := by sorry

end ChanTomoNB
