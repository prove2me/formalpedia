-- Prove2me | Theorems.Thm_DeFinettiSDP_NoSymm_lemma_D_1
-- name    : DeFinettiSDP.NoSymm.lemma_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:24.553948+00:00
-- url     : https://prove2.me/theorems/7d8e8fbf-42e1-4855-a86c-19b69ab5038e
-- title:
--   Lemma D.1, p. 29 — two-design measurement preserves trace norm up to d_B²(d_B+1)
-- statement:
--   Let $(P_z)_{z=1}^t$ be a state two-design on a $d_B$-dimensional system $B$, and let $M_z=(d_B/t)P_z$ be its measurement. For any finite-dimensional side system $A$ and any Hermitian operator $\xi_{AB}$,
--
--   $$
--   \left\|(I_A\otimes M_B)(\xi_{AB})\right\|_1
--   \ge \frac{1}{d_B^2(d_B+1)}\|\xi_{AB}\|_1.
--   $$
--
--   The bound controls the loss of trace-norm distinguishability under measurement without depending on the size of $A$. It supplies the concrete distortion factor in the goal theorem.
--
--   **Formalization Note** The design requires $t>0$. Its symmetric projector is $(I+F)/2$ on $B\otimes B$, and the trace norm is unnormalized.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, Lemma D.1, p. 29

import Mathlib
import Definitions.Def_DeFinettiSDP_NoSymm_Quantum

namespace DeFinettiSDP.NoSymm

/-- Lemma D.1, p. 29. The design has `t > 0` outcomes; its second moment uses
`Psym dB = (I + swap)/2` on `B ⊗ B`. The arbitrary Hermitian input may have
any finite side system A. -/
theorem lemma_D_1 {dA dB t : ℕ}
    (P : Fin t → Matrix (Fin dB) (Fin dB) ℂ)
    (ht : 0 < t) (hP : DeFinettiSDP.Hierarchy.IsStateTwoDesign P)
    (ξ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hξ : ξ.IsHermitian) :
    (1 / ((dB : ℝ) ^ 2 * ((dB : ℝ) + 1))) * WildeQIT.traceNorm ξ ≤
      WildeQIT.traceNorm (measB (DeFinettiSDP.Hierarchy.designMeas P) ξ) := by sorry

end DeFinettiSDP.NoSymm
