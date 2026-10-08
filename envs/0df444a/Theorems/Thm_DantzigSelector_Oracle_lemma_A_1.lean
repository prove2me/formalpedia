-- Prove2me | Theorems.Thm_DantzigSelector_Oracle_lemma_A_1
-- name    : DantzigSelector.Oracle.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:49:37.675737+00:00
-- url     : https://prove2.me/theorems/967a0d0e-2c8e-44e1-82dc-f18a265cd92a
-- title:
--   Lemma A.1 — dual sparse reconstruction, $\ell_2$ version
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ with columns $X_1,\dots,X_p$, let $S\ge1$ with $3S\le p$, and write $\delta=\delta_{2S}$ for the restricted isometry constant and $\theta=\theta_{S,2S}$ for the restricted orthogonality constant of $X$. Assume $\delta+\theta<1$. Let $T\subseteq\{1,\dots,p\}$ with $|T|\le2S$ and let $c\in\mathbb R^p$ be supported on $T$. Then there exist a vector $\beta$ supported on $T$ and an exceptional set $E$ disjoint from $T$ such that
--
--   1. $|E|\le S$ (6.1);
--   2. $\langle X\beta,X_j\rangle=c_j$ for all $j\in T$ (6.2);
--   3. $|\langle X\beta,X_j\rangle|\le\dfrac{\theta}{(1-\delta)\sqrt S}\|c\|_{\ell_2}$ for all $j\notin T\cup E$ (6.3);
--   4. $\Big(\sum_{j\in E}|\langle X\beta,X_j\rangle|^2\Big)^{1/2}\le\dfrac{\theta}{1-\delta}\|c\|_{\ell_2}$ (6.4);
--   5. $\|\beta\|_{\ell_2}\le\dfrac{1}{1-\delta}\|c\|_{\ell_2}$ (6.5);
--   6. $\|\beta\|_{\ell_1}\le\dfrac{\sqrt{2S}}{1-\delta}\|c\|_{\ell_2}$ (6.6).
--
--   The vector $X\beta$ interpolates the prescribed correlations $c$ on $T$ while its correlations with all other columns are small, except on a small exceptional set where they are small in $\ell_2$. Iterating this lemma yields Corollary A.2.
--
--   **Formalization Note** $\langle X\beta,X_j\rangle$ is written $\sum_i (X\beta)_i X_{ij}$. Since $c$ is supported on $T$, $\|c_T\|_{\ell_2}=\|c\|_{\ell_2}$. The hypothesis $3S\le p$ is the domain on which the paper defines $\theta_{S,2S}$ ((1.5) is stated for $S+S'\le p$). The appendix's standing unit-norm assumption on the columns is not needed by the statement or its proof and is not assumed.
-- source:
--   Candès & Tao, The Dantzig Selector: Statistical Estimation When p Is Much Larger than n, arXiv:math/0506081v3, p. 35, Lemma A.1, Eqs. (6.1)-(6.6)

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model
import Definitions.Def_DantzigSelector_Oracle_Model

open CandesTao.Decoding DantzigSelector.Sparse

namespace DantzigSelector.Oracle

/-- Candès–Tao (2007), Lemma A.1 (dual sparse reconstruction, ℓ2 version), p. 35, with
`δ = δ_{2S}` and `θ = θ_{S,2S}`: for `c` supported on `T`, `|T| ≤ 2S`, there are `β` supported
on `T` and an exceptional set `E` disjoint from `T` with `|E| ≤ S` (6.1),
`⟨Xβ, X_j⟩ = c_j` on `T` (6.2), `|⟨Xβ, X_j⟩| ≤ θ/((1 − δ)√S) ‖c‖` off `T ∪ E` (6.3),
`(∑_{j∈E} |⟨Xβ, X_j⟩|²)^{1/2} ≤ θ/(1 − δ) ‖c‖` (6.4), `‖β‖_{ℓ2} ≤ ‖c‖/(1 − δ)` (6.5) and
`‖β‖_{ℓ1} ≤ √(2S)/(1 − δ) ‖c‖` (6.6). -/
theorem lemma_A_1 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (S : ℕ) (hS : 1 ≤ S)
    (hSp : 3 * S ≤ p)
    (hδθ : restrictedIsometryConst X (2 * S) + restrictedOrthogonalityConst X S (2 * S) < 1)
    (T : Finset (Fin p)) (hT : T.card ≤ 2 * S) (c : Fin p → ℝ) (hc : SupportedOn c T) :
    ∃ (β : Fin p → ℝ) (E : Finset (Fin p)),
      SupportedOn β T ∧ Disjoint E T ∧
      E.card ≤ S ∧
      (∀ j ∈ T, ∑ i, (X.mulVec β) i * X i j = c j) ∧
      (∀ j : Fin p, j ∉ T ∪ E →
        |∑ i, (X.mulVec β) i * X i j| ≤
          restrictedOrthogonalityConst X S (2 * S) /
            ((1 - restrictedIsometryConst X (2 * S)) * Real.sqrt S) * l2Norm c) ∧
      Real.sqrt (∑ j ∈ E, (∑ i, (X.mulVec β) i * X i j) ^ 2) ≤
        restrictedOrthogonalityConst X S (2 * S) /
          (1 - restrictedIsometryConst X (2 * S)) * l2Norm c ∧
      l2Norm β ≤ 1 / (1 - restrictedIsometryConst X (2 * S)) * l2Norm c ∧
      l1Norm β ≤
        Real.sqrt (2 * (S : ℝ)) / (1 - restrictedIsometryConst X (2 * S)) * l2Norm c := by sorry

end DantzigSelector.Oracle
