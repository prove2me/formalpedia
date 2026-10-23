-- Prove2me | Theorems.Thm_BinaryExtForm_HypercubeRank_lemma_4_20
-- name    : BinaryExtForm.HypercubeRank.lemma_4_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:34.662436+00:00
-- url     : https://prove2.me/theorems/a4f77157-198d-4641-accb-19097ad78578
-- title:
--   Lemma 4.20, p. 13 — 2^{f_B(α_1,…,α_ℓ)} divides α_j + 1 for every j
-- statement:
--   Let $B$ be a $d$-hypercube binarization with hypercube graph $G(B)$ and let $\alpha_1, \dots, \alpha_\ell \in \{0, \dots, 2^d - 2\}$. Then for every $j \in [\ell]$,
--   $$2^{f_B(\alpha_1, \dots, \alpha_\ell)} \ \text{divides}\ \alpha_j + 1.$$
--
--   The number of uncrossed directions of an arbitrary hypercube binarization is thus bounded by the $2$-adic valuations of the $\alpha_j + 1$, which is exactly what the logarithmic binarization attains (Corollary 4.22).
--
--   **Formalization Note.** $\alpha_j + 2 \le 2^d$ encodes the range $\{0,\dots,2^d-2\}$. For $\ell = 0$ the statement is vacuous, as on the page.
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, p. 13, Lemma 4.20

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

namespace BinaryExtForm.HypercubeRank
theorem lemma_4_20 {d ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsHypercubeBinarization d B)
    (α : Fin ℓ → ℕ) (hα : ∀ j, α j + 2 ≤ 2 ^ d) :
    ∀ j, 2 ^ fB B α ∣ α j + 1 := by sorry
end BinaryExtForm.HypercubeRank
