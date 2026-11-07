-- Prove2me | Theorems.Thm_AvgCaseTI_lemma_3_2
-- name    : AvgCaseTI.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:42:22.75891+00:00
-- url     : https://prove2.me/theorems/ea6067ee-b0ee-4f0f-8046-72132c65aa3d
-- title:
--   Lemma 3.2 — conjugate codes have conjugate hulls
-- statement:
--   Let $\mathbb F$ be a field, $T\in\mathrm{GL}(n,\mathbb F)$ and $\mathcal C\le\mathrm M(n,\mathbb F)$ a matrix code. Then
--   $$
--   H\bigl(T\mathcal CT^{-1}\bigr)=T\,H(\mathcal C)\,T^{-1},
--   $$
--   where $H$ is the hull with respect to the trace form $\mathrm{Tr}(XY)$. In particular, if two codes $\mathcal A,\mathcal B\le\mathrm M(n,q)$ are conjugate, then their hulls $H(\mathcal A)$ and $H(\mathcal B)$ are conjugate (by the same matrix).
--
--   This is why the hull is a canonical object of the algebra-isomorphism algorithm: an isomorphism of algebras conjugates the slice codes, hence their hulls.
--
--   Differences from the source:
--
--   - generalization: codes over F_q; "if A and B are conjugate then H(A) and H(B) are conjugate" → every field; H(TCT⁻¹) = T·H(C)·T⁻¹ for every T and C; reason: with A = TBT⁻¹ the equation gives H(A) = T·H(B)·T⁻¹, the printed lemma; F_q is a special case
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Lemma 3.2, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_AvgCaseTI_hull

set_option autoImplicit false

namespace AvgCaseTI

/-- **Lemma 3.2 (conjugation commutes with taking the hull).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Lemma 3.2, p.16
(PDF p.18), citing [CL25, Lemma 3]: "Let A and B ≤ M(n, q). If A and B are conjugate, then H(A) and
H(B) are conjugate."

Stated with the conjugating matrix made explicit: for every invertible `T` and every matrix code `𝒞`,
`H(T𝒞T^{−1}) = T·H(𝒞)·T^{−1}`. If `𝒜 = T𝓑T^{−1}` then `H(𝒜) = T·H(𝓑)·T^{−1}`, which is the printed
lemma.

**Formalization Note.** Holds over every field (the paper's `F_q` is a special case). -/
theorem lemma_3_2 {K : Type*} [Field K] {n : ℕ} (T : GL (Fin n) K)
    (C : Submodule K (Mat K n)) :
    hull (conjCode T C) = conjCode T (hull C) := by sorry

end AvgCaseTI
