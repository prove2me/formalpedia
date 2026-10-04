-- Prove2me | Theorems.Thm_DantzigSelector_Sparse_lemma_3_1
-- name    : DantzigSelector.Sparse.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:40:39.793997+00:00
-- url     : https://prove2.me/theorems/163e1c8e-7251-46a3-8bc5-92f4cc6fcf0f
-- title:
--   Lemma 3.1 — $\ell_2$ control of $h$ on $T_{01}$ and on all coordinates
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ have unit-normed columns, let $S\ge1$ with $3S\le p$, and write $\delta:=\delta_{2S}$ for the $2S$-restricted isometry constant and $\theta:=\theta_{S,2S}$ for the $S,2S$-restricted orthogonality constant of $X$ (Eqs. (1.3) and (1.5)). Assume $\delta+\theta<1$.
--
--   Let $T_0\subseteq\{1,\dots,p\}$ have cardinality $S$, let $h\in\mathbb R^p$, let $T_1$ be the $S$ largest positions of $h$ outside of $T_0$, and put $T_{01}=T_0\cup T_1$. Then
--   $$
--   \|h\|_{\ell_2(T_{01})}\le\frac{1}{1-\delta}\,\|X_{T_{01}}^{T}Xh\|_{\ell_2}+\frac{\theta}{(1-\delta)S^{1/2}}\,\|h\|_{\ell_1(T_0^c)}
--   $$
--   and
--   $$
--   \|h\|_{\ell_2}^2\le\|h\|_{\ell_2(T_{01})}^2+S^{-1}\,\|h\|_{\ell_1(T_0^c)}^2 .
--   $$
--   Here $\|X_{T_{01}}^{T}Xh\|_{\ell_2}=\bigl(\sum_{j\in T_{01}}\langle Xh,X_j\rangle^2\bigr)^{1/2}$.
--
--   The lemma converts the cone and tube constraints on the error $h$ of the Dantzig selector into an $\ell_2$ bound. It is the deterministic heart of Theorem 1.1 and is used again in the proof of Theorem 1.2.
--
--   **Formalization Note** $\delta_{2S}$ and $\theta_{S,2S}$ are the published `restrictedIsometryConst X (2*S)` and `restrictedOrthogonalityConst X S (2*S)` (the least admissible constants), following the paper's convention "$\delta:=\delta_{2S}$ and $\theta:=\theta_{S,2S}$" (p. 9). The hypotheses $1\le S$ and $3S\le p$ record that $\theta_{S,2S}$ is defined only for $S+2S\le p$ (p. 3). Both inequalities are stated as one conjunction.
-- source:
--   Candès & Tao, The Dantzig Selector: Statistical Estimation When p Is Much Larger than n, arXiv:math/0506081v3, p. 17, Lemma 3.1 (δ := δ_2S, θ := θ_S,2S as fixed on p. 9 with (1.14))

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model
open CandesTao.Decoding

namespace DantzigSelector.Sparse

/-- Lemma 3.1, with `δ := δ_{2S}` and `θ := θ_{S,2S}`: for `T0` of cardinality `S` and `T1` the
`S` largest positions of `h` outside `T0`, with `T01 = T0 ∪ T1`,
`‖h‖_{ℓ2(T01)} ≤ (1-δ)⁻¹ ‖X_{T01}ᵀ X h‖_{ℓ2} + θ ((1-δ) S^{1/2})⁻¹ ‖h‖_{ℓ1(T0ᶜ)}` and
`‖h‖²_{ℓ2} ≤ ‖h‖²_{ℓ2(T01)} + S⁻¹ ‖h‖²_{ℓ1(T0ᶜ)}`. -/
theorem lemma_3_1 {n p S : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hS : 1 ≤ S) (hSp : 3 * S ≤ p)
    (hX : UnitNormColumns X)
    (hRIP : restrictedIsometryConst X (2 * S) + restrictedOrthogonalityConst X S (2 * S) < 1)
    (T0 T1 : Finset (Fin p)) (hT0 : T0.card = S) (h : Fin p → ℝ)
    (hT1 : IsTopBlock h T0 T1 S) :
    l2On h (T0 ∪ T1) ≤
        1 / (1 - restrictedIsometryConst X (2 * S)) *
            Real.sqrt (∑ j ∈ T0 ∪ T1, (∑ i, X i j * X.mulVec h i) ^ 2) +
          restrictedOrthogonalityConst X S (2 * S) /
              ((1 - restrictedIsometryConst X (2 * S)) * Real.sqrt S) * l1On h T0ᶜ ∧
      l2Norm h ^ 2 ≤ l2On h (T0 ∪ T1) ^ 2 + (S : ℝ)⁻¹ * l1On h T0ᶜ ^ 2 := by sorry

end DantzigSelector.Sparse
