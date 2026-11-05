-- Prove2me | Theorems.Thm_Chi2QEC_errorImages_finrank_of_nondegenerate
-- name    : Chi2QEC.errorImages_finrank_of_nondegenerate
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:27.336198+00:00
-- url     : https://prove2.me/theorems/6f7d83c0-8dc5-48f8-85d1-5f21c8516240
-- title:
--   Eq. (112) — $D_{\mathrm{err}}=(\#\text{errors})\dim C$ (corrected: nondegenerate code)
-- statement:
--   Let $C$ be a subspace of a finite-dimensional Hilbert space and $(E_h)_{h\in\kappa}$ a finite family of operators. If $C$ satisfies the error-correction condition (23) for this family and is nondegenerate for it, then the corrupted code subspace has dimension
--   $$
--   \dim\sum_{h\in\kappa}E_h(C)=|\kappa|\cdot\dim C.
--   $$
--   For the $1+3n$ single-photon-loss errors and $\dim C=b^k$, the right side is $D_{\mathrm{err}}=(1+3n)b^k$ of (112), so $D_{\mathrm{err}}$ does not exceed $D_{\mathrm{loss}}$.
--
--   This is the step of the proof of Theorem 5 in which correctability is converted into a dimension count.
--
--   Differences from the source:
--   - correction: no nondegeneracy hypothesis → IsNondegenerate C E; reason: false without it even at q ≥ 2: for q = n = 2 and C = Span{|0,0,1⟩|0,0,1⟩}, (23) holds since C is one-dimensional, but only I, a_{p,1}, a_{p,2} are nonzero on C, so the span has dimension 3 < 7 = (1 + 3·2)·1
--   - generalization: the 1 + 3n loss errors on a code in H_{q−1}^{⊗n} → any finite error family on any finite-dimensional space; reason: it specializes at E = lossError n q, whose index type has cardinality 1 + 3n
--   - generalization: D_err cannot exceed D_loss → finrank (corruptedSubspace C E) = card κ * finrank C; reason: the equality contains the inequality of the page, and the opposite inequality always holds
--   - reading: D_err, the "total dimension of photon-loss errors", and D_loss → card κ * finrank C, and finrank of the span of the error images; reason: Σ_{j≤1} C(3n, j) = 1 + 3n counts the errors, and D_loss is the dimension of "the corrupted code subspace"
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, (112) and the sentence after it, proof of Theorem 5, p.17

import Mathlib
import Definitions.Def_Chi2QEC_SatisfiesKL
import Definitions.Def_Chi2QEC_IsNondegenerate
import Definitions.Def_Chi2QEC_corruptedSubspace

namespace Chi2QEC

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, (112) and the sentence after it, proof of Theorem 5, p.17: for a nondegenerate
code satisfying (23), the error images of the code have total dimension
`D_err = (number of errors) · dim C`, so `D_err` does not exceed `D_loss`.

**Formalization Note.** Stated for any finite-dimensional space and finite error family; the
paper's case is `κ = Option (Fin n × Fin 3)`, of cardinality `1 + 3n`. Nondegeneracy is a
correction: the page does not assume it, and without it the claim fails. For `q = n = 2` and `C`
spanned by `|0,0,1⟩|0,0,1⟩`, condition (23) holds, but only three error images are nonzero. The
direction `≤` of the equality always holds, so the equality says the same as the page's
`D_err ≤ D_loss`. -/
theorem errorImages_finrank_of_nondegenerate {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (C : Submodule ℂ (EuclideanSpace ℂ ι)) (E : κ → Matrix ι ι ℂ)
    (hKL : SatisfiesKL C E) (hnd : IsNondegenerate C E) :
    Module.finrank ℂ (corruptedSubspace C E) = Fintype.card κ * Module.finrank ℂ C := by sorry

end Chi2QEC
