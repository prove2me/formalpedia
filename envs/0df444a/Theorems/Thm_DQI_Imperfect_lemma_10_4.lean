-- Prove2me | Theorems.Thm_DQI_Imperfect_lemma_10_4
-- name    : DQI.Imperfect.lemma_10_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:03:10.662017+00:00
-- url     : https://prove2.me/theorems/bbeabecf-cae0-4ee8-8af2-7567dcdf2a42
-- title:
--   Lemma 10.4 — norm of the postselected state
-- statement:
--   Let $B\in\mathbb F_2^{m\times n}$, let $v\in\mathbb F_2^m$, and let $\mathrm{dec}$ be a deterministic syndrome decoder. For weights $w_0,\ldots,w_\ell$ with $\ell\le m$, let $\widetilde P_D(f)$ be the unnormalized postselected syndrome state and $\varepsilon_k=|F_k|/\binom m k$. Then
--
--   $$
--   \|\widetilde P_D(f)\|^2=\sum_{k=0}^{\ell}w_k^2(1-\varepsilon_k)\le\sum_{k=0}^{\ell}w_k^2.
--   $$
--
--   This identity gives the normalization and postselection probability used by the main bound.
--
--   **Formalization Note** The condition $\ell\le m$ ensures that every binomial denominator is positive.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 40, Lemma 10.4, (174)

import Mathlib
import Definitions.Def_DQI_Imperfect_Setting

namespace DQI.Imperfect

theorem lemma_10_4 (m n ℓ : ℕ) (hℓ : ℓ ≤ m)
    (B : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2) (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (w : Fin (ℓ + 1) → ℝ) :
    (∑ s, (PtD B v dec ℓ w s) ^ 2) =
        (∑ k, (w k) ^ 2 * (1 - epsk B dec k.val)) ∧
      (∑ k, (w k) ^ 2 * (1 - epsk B dec k.val)) ≤ w ⬝ᵥ w := by sorry

end DQI.Imperfect
