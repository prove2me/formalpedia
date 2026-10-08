-- Prove2me | Theorems.Thm_DantzigSelector_Oracle_lemma_3_1
-- name    : DantzigSelector.Oracle.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:49:50.132808+00:00
-- url     : https://prove2.me/theorems/907be98b-e7e5-4002-b198-6b7e53e9f2ba
-- title:
--   Lemma 3.1 — $\ell_2$ control on $T_{01}$ from $X_{T_{01}}^TXh$ and $\|h\|_{\ell_1(T_0^c)}$
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $S\ge1$ with $3S\le p$, and write $\delta=\delta_{2S}$, $\theta=\theta_{S,2S}$ with $\delta+\theta<1$. Let $T_0\subseteq\{1,\dots,p\}$ have cardinality $S$, let $h\in\mathbb R^p$, let $T_1$ be a set of the $S$ largest positions of $h$ outside of $T_0$ (ties broken arbitrarily), and put $T_{01}=T_0\cup T_1$. Then
--   $$\|h\|_{\ell_2(T_{01})}\le\frac{1}{1-\delta}\|X_{T_{01}}^TXh\|_{\ell_2}+\frac{\theta}{(1-\delta)S^{1/2}}\|h\|_{\ell_1(T_0^c)}$$
--   and
--   $$\|h\|_{\ell_2}^2\le\|h\|_{\ell_2(T_{01})}^2+S^{-1}\|h\|_{\ell_1(T_0^c)}^2.$$
--
--   Here $\|X_{T_{01}}^TXh\|_{\ell_2}=(\sum_{j\in T_{01}}\langle Xh,X_j\rangle^2)^{1/2}$. The lemma converts the cone and tube constraints satisfied by the error vector of the Dantzig selector into an $\ell_2$ bound; it is used in the proofs of both Theorem 1.1 and Theorem 1.2.
--
--   **Formalization Note** The paper's $\delta,\theta$ are $\delta_{2S}$ and $\theta_{S,2S}$, fixed with (1.14) on p. 9 ("above and below"). Both inequalities are stated as one conjunction. $3S\le p$ is the domain of $\theta_{S,2S}$ and guarantees that $T_1$ exists. No column normalization is assumed. The same statement is drafted in the companion mission on Theorem 1.1.
-- source:
--   Candès & Tao, The Dantzig Selector: Statistical Estimation When p Is Much Larger than n, arXiv:math/0506081v3, p. 17, Lemma 3.1

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model
import Definitions.Def_DantzigSelector_Oracle_Model

open CandesTao.Decoding DantzigSelector.Sparse

namespace DantzigSelector.Oracle

/-- Candès–Tao (2007), Lemma 3.1, p. 17, with `δ = δ_{2S}`, `θ = θ_{S,2S}`: if `|T0| = S`,
`δ + θ < 1`, and `T1` is a set of the `S` largest positions of `h` outside `T0`, then with
`T01 = T0 ∪ T1`,
`‖h‖_{ℓ2(T01)} ≤ (1 − δ)⁻¹ ‖X_{T01}^T X h‖_{ℓ2} + θ/((1 − δ)√S) ‖h‖_{ℓ1(T0ᶜ)}` and
`‖h‖²_{ℓ2} ≤ ‖h‖²_{ℓ2(T01)} + S⁻¹ ‖h‖²_{ℓ1(T0ᶜ)}`. -/
theorem lemma_3_1 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (S : ℕ) (hS : 1 ≤ S)
    (hSp : 3 * S ≤ p)
    (hδθ : restrictedIsometryConst X (2 * S) + restrictedOrthogonalityConst X S (2 * S) < 1)
    (T0 T1 : Finset (Fin p)) (hT0 : T0.card = S) (h : Fin p → ℝ)
    (hT1 : IsTopBlock h T0 T1 S) :
    l2On h (T0 ∪ T1) ≤
        1 / (1 - restrictedIsometryConst X (2 * S)) *
            Real.sqrt (∑ j ∈ T0 ∪ T1, (∑ i, X i j * (X.mulVec h) i) ^ 2) +
          restrictedOrthogonalityConst X S (2 * S) /
            ((1 - restrictedIsometryConst X (2 * S)) * Real.sqrt S) * l1On h T0ᶜ ∧
      l2Norm h ^ 2 ≤ l2On h (T0 ∪ T1) ^ 2 + (S : ℝ)⁻¹ * l1On h T0ᶜ ^ 2 := by sorry

end DantzigSelector.Oracle
