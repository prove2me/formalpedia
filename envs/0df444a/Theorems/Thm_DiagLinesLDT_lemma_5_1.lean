-- Prove2me | Theorems.Thm_DiagLinesLDT_lemma_5_1
-- name    : DiagLinesLDT.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:51:07.247231+00:00
-- url     : https://prove2.me/theorems/bdcacb0c-11dd-4e5d-9a9a-19d9430df278
-- title:
--   Lemma 5.1 — maximally entangled-state identity
-- statement:
--   For all operators $M,N$ on $\mathcal H$,
--
--   $$\langle\Phi|M\otimes N|\Phi\rangle=\frac{1}{\dim\mathcal H}\operatorname{Tr}(MN^{\mathrm T}).$$
--
--   This reduces every expectation in the mission to a trace, and it is why Bob's operators are transposes of Alice's.
--
--   Differences from the source:
--   - generalization: H = ℂ^{𝔽_q³} → any finite index type ι; reason: the computation is on matrix entries and specializes at ι = 𝔽_q³
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Lemma 5.1, p.14

import Mathlib
import Definitions.Def_DiagLinesLDT_Gamma

open scoped Kronecker

namespace DiagLinesLDT

/-- Maximally entangled-state identity.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), Lemma 5.1, p.14.

**Formalization Note** Stated for every finite index type `ι`; the source has `ι = 𝔽_q³`. The
expectation here is the complex number, not its real part. -/
theorem lemma_5_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (M N : Matrix ι ι ℂ) :
    star (maxEnt ι) ⬝ᵥ ((M ⊗ₖ N).mulVec (maxEnt ι)) =
      (Fintype.card ι : ℂ)⁻¹ * (M * N.transpose).trace := by sorry

end DiagLinesLDT
