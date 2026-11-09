-- Prove2me | Theorems.Thm_CondGeoVerif_lemma_B_3
-- name    : CondGeoVerif.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:40:29.021044+00:00
-- url     : https://prove2.me/theorems/547a1b3a-9e4b-45d4-b89d-9bf2f2e0b018
-- title:
--   Lemma B.3 — chaos contraction $|\mathbb E[b(G)c(H)]|\le\|R\|_{\mathrm{op}}^s\|b\|_2\|c\|_2$
-- statement:
--   Let $(G,H)$ be jointly standard Gaussian vectors in $\mathbb R^k$ with cross-covariance $R=\mathbb E[GH^\top]$ and $\|R\|_{\mathrm{op}}\le1$. If $b,c\in L^2(\gamma_k)$ are orthogonal to every polynomial of total degree less than $s$, $s\ge1$, then
--   $$|\mathbb E[b(G)c(H)]|\le\|R\|_{\mathrm{op}}^s\,\|b\|_2\,\|c\|_2 .$$
--   The statement includes singular joint Gaussian laws and $\|R\|_{\mathrm{op}}=1$.
--
--   Differences from the source:
--   - encoding: jointly standard Gaussian (G, H) with cross-covariance R → the law of (G, RᵀG + (I − RᵀR)^{1/2}G′), G′ an independent copy; reason: this is the unique jointly Gaussian law with standard marginals and cross-covariance R
--   - encoding: ‖R‖_op ≤ 1; b, c ∈ L²(γ_k) orthogonal to polynomials of degree < s → I − RᵀR positive semidefinite; MemLp 2 and ∫ b·q dγ_k = 0 for every real polynomial q of total degree < s; reason: equivalent formulations
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Lemma B.3, p.26 (PDF p.29)

import Mathlib
import Definitions.Def_CondGeoVerif_hiddenErr

set_option autoImplicit false

open MeasureTheory

namespace CondGeoVerif

/-- **Lemma B.3 (A standard chaos contraction)** (Chen, *The Conditional Geometry of Statistical
Verification*, manuscript, October 2026, sha256 07a66d18…, §B.3, p.26 = PDF p.29). Let `(G, H)`
be jointly standard Gaussian vectors in `ℝᵏ` with cross-covariance `R = E[GHᵀ]` and
`‖R‖_op ≤ 1`. If `b, c ∈ L²(γ_k)` are orthogonal to every polynomial of total degree less than `s`,
then `|E[b(G)c(H)]| ≤ ‖R‖_op^s ‖b‖₂‖c‖₂`. This holds for `s ≥ 1`, including singular joint
Gaussian laws and `‖R‖_op = 1`.

**Formalization Note** The joint law is `corrPair R` (`G ∼ N(0, I_k)`,
`H = RᵀG + (I − RᵀR)^{1/2}G'`), the unique jointly Gaussian law with standard marginals and
cross-covariance `R`. `‖R‖_op ≤ 1` is `IsContraction R`; `‖R‖_op` is the Euclidean operator norm
`opNorm`. Orthogonality is against every real polynomial in `k` variables of total degree `< s`. -/
theorem lemma_B_3 {k : ℕ} (R : Matrix (Fin k) (Fin k) ℝ) (hR : IsContraction R) (s : ℕ)
    (hs : 1 ≤ s) (b c : Vec k → ℝ) (hb : MemLp b 2 (gauss k)) (hc : MemLp c 2 (gauss k))
    (hbo : ∀ q : MvPolynomial (Fin k) ℝ, q.totalDegree < s →
      ∫ z, b z * MvPolynomial.eval (fun i => z i) q ∂(gauss k) = 0)
    (hco : ∀ q : MvPolynomial (Fin k) ℝ, q.totalDegree < s →
      ∫ z, c z * MvPolynomial.eval (fun i => z i) q ∂(gauss k) = 0) :
    |∫ p, b p.1 * c p.2 ∂(corrPair R)| ≤
      opNorm R ^ s * Real.sqrt (∫ z, b z ^ 2 ∂(gauss k)) * Real.sqrt (∫ z, c z ^ 2 ∂(gauss k)) := by sorry

end CondGeoVerif
