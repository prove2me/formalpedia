-- Prove2me | Theorems.Thm_DantzigSelector_Oracle_corollary_A_2
-- name    : DantzigSelector.Oracle.corollary_A_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:49:40.417983+00:00
-- url     : https://prove2.me/theorems/d16891bb-c24c-4696-bcab-62881f1c7697
-- title:
--   Corollary A.2 — dual sparse reconstruction, $\ell_\infty$ version
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ with columns $X_1,\dots,X_p$, let $S\ge1$ with $3S\le p$, and write $\delta=\delta_{2S}$, $\theta=\theta_{S,2S}$. Assume $\delta+\theta<1$. Let $T\subseteq\{1,\dots,p\}$ with $|T|\le S$ and let $c\in\mathbb R^p$ be supported on $T$. Then there exists $\beta\in\mathbb R^p$ such that $\langle X\beta,X_j\rangle=c_j$ for all $j\in T$ (6.2),
--   $$|\langle X\beta,X_j\rangle|\le\frac{\theta}{(1-\delta-\theta)\sqrt S}\,\|c\|_{\ell_2}\quad\text{for all } j\notin T\qquad(6.8),$$
--   and
--   $$\|\beta\|_{\ell_2}\le\frac{1}{1-\delta-\theta}\|c\|_{\ell_2}\quad(6.9),\qquad \|\beta\|_{\ell_1}\le\frac{\sqrt{2S}}{1-\delta-\theta}\|c\|_{\ell_2}\quad(6.10).$$
--
--   Unlike Lemma A.1 there is no exceptional set: every correlation off $T$ is uniformly small. This is the tool that builds the "pseudo-hard-thresholded" vector of Corollary A.3.
--
--   **Formalization Note** The vector $\beta$ is not required to be supported on $T$. The hypothesis $\delta+\theta<1$ is not repeated in the corollary's sentence on p. 36; it is the standing hypothesis of Lemma A.1, which the proof iterates, and the proof's geometric series needs $\theta/(1-\delta)<1$. $3S\le p$ is the domain of $\theta_{S,2S}$. No column normalization is assumed.
-- source:
--   Candès & Tao, The Dantzig Selector: Statistical Estimation When p Is Much Larger than n, arXiv:math/0506081v3, p. 36, Corollary A.2, Eqs. (6.8)-(6.10)

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model
import Definitions.Def_DantzigSelector_Oracle_Model

open CandesTao.Decoding DantzigSelector.Sparse

namespace DantzigSelector.Oracle

/-- Candès–Tao (2007), Corollary A.2 (dual sparse reconstruction, ℓ∞ version), p. 36, with
`δ = δ_{2S}`, `θ = θ_{S,2S}` and the standing hypothesis `δ + θ < 1` of Lemma A.1: for `c`
supported on `T`, `|T| ≤ S`, there is `β` (not necessarily supported on `T`) with
`⟨Xβ, X_j⟩ = c_j` on `T` (6.2), `|⟨Xβ, X_j⟩| ≤ θ/((1 − δ − θ)√S) ‖c‖` off `T` (6.8),
`‖β‖_{ℓ2} ≤ ‖c‖/(1 − δ − θ)` (6.9) and `‖β‖_{ℓ1} ≤ √(2S)/(1 − δ − θ) ‖c‖` (6.10). -/
theorem corollary_A_2 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (S : ℕ) (hS : 1 ≤ S)
    (hSp : 3 * S ≤ p)
    (hδθ : restrictedIsometryConst X (2 * S) + restrictedOrthogonalityConst X S (2 * S) < 1)
    (T : Finset (Fin p)) (hT : T.card ≤ S) (c : Fin p → ℝ) (hc : SupportedOn c T) :
    ∃ β : Fin p → ℝ,
      (∀ j ∈ T, ∑ i, (X.mulVec β) i * X i j = c j) ∧
      (∀ j : Fin p, j ∉ T →
        |∑ i, (X.mulVec β) i * X i j| ≤
          restrictedOrthogonalityConst X S (2 * S) /
            ((1 - restrictedIsometryConst X (2 * S) - restrictedOrthogonalityConst X S (2 * S)) *
              Real.sqrt S) * l2Norm c) ∧
      l2Norm β ≤
        1 / (1 - restrictedIsometryConst X (2 * S) - restrictedOrthogonalityConst X S (2 * S)) *
          l2Norm c ∧
      l1Norm β ≤
        Real.sqrt (2 * (S : ℝ)) /
          (1 - restrictedIsometryConst X (2 * S) - restrictedOrthogonalityConst X S (2 * S)) *
            l2Norm c := by sorry

end DantzigSelector.Oracle
