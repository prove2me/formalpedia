-- Prove2me | Theorems.Thm_BinaryExtForm_HypercubeRank_corollary_4_22
-- name    : BinaryExtForm.HypercubeRank.corollary_4_22
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:32.015741+00:00
-- url     : https://prove2.me/theorems/b3a5d0d2-7ee6-4135-8f22-00973d9b5fa5
-- title:
--   Corollary 4.22, p. 14 — f_{B^L}(α_1,…,α_ℓ) = max{t : 2^t divides α_j + 1 for all j}
-- statement:
--   Let $B^L = B^L(d)$ be the logarithmic binarization with hypercube graph $G(B^L)$, and let $\alpha_1, \dots, \alpha_\ell \in \{0, \dots, 2^d - 2\}$ with $\ell \ge 1$. Then
--   $$f_{B^L}(\alpha_1, \dots, \alpha_\ell) = \max\{t : 2^t \text{ divides } \alpha_j + 1 \ \forall j \in [\ell]\}.$$
--
--   Together with Corollary 4.19 this gives the explicit formula $\operatorname{rk}_{B^L}(\alpha_1,\dots,\alpha_\ell) = d - \max\{t : 2^t \mid \alpha_j + 1\ \forall j\}$, and together with Lemma 4.20 it shows that $B^L$ maximizes $f_B$ among hypercube binarizations.
--
--   **Formalization Note.** The hypothesis $\ell \ge 1$ (`0 < ℓ`) is added: for $\ell = 0$ every $t$ qualifies, so the maximum does not exist, while $f_{B^L}() = d$. The maximum is stated with `IsGreatest`, not `sSup`, so it is asserted to exist. $\alpha_j + 2 \le 2^d$ encodes the range.
-- source:
--   Aprile, Conforti, Di Summa, Binary extended formulations and sequential convexification, arXiv:2106.00354v1, p. 14, Corollary 4.22

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model

namespace BinaryExtForm.HypercubeRank
theorem corollary_4_22 {d ℓ : ℕ} (hℓ : 0 < ℓ) (α : Fin ℓ → ℕ) (hα : ∀ j, α j + 2 ≤ 2 ^ d) :
    IsGreatest {t : ℕ | ∀ j, 2 ^ t ∣ α j + 1} (fB (BL d) α) := by sorry
end BinaryExtForm.HypercubeRank
