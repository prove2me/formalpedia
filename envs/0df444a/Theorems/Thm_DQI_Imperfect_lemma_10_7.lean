-- Prove2me | Theorems.Thm_DQI_Imperfect_lemma_10_7
-- name    : DQI.Imperfect.lemma_10_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:03:31.022563+00:00
-- url     : https://prove2.me/theorems/425923f4-7980-4356-8401-34aec29829d7
-- title:
--   Lemma 10.7 — decoder-error matrix bound
-- statement:
--   Let $\varepsilon_k=|F_k|/\binom m k$ be the misidentification fraction in each Hamming shell and let $\varepsilon=\max_{0\le k\le\ell}\varepsilon_k$. The symmetric error matrix $E^{(m,\ell,F)}$ of (181) satisfies the real Euclidean operator-norm bound
--
--   $$
--   \|E^{(m,\ell,F)}\|_{2\to2}\le 2\varepsilon(m+1).
--   $$
--
--   This bounds the error term in the average objective matrix uniformly over the choice of weights.
--
--   **Formalization Note** The Lean statement uses the equivalent bound $|u^\top Eu|\le2\varepsilon(m+1)u^\top u$ for every real vector $u$, and assumes $\ell\le m$.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 43, Lemma 10.7, (196)

import Mathlib
import Definitions.Def_DQI_Imperfect_Setting

namespace DQI.Imperfect

theorem lemma_10_7 (m n ℓ : ℕ) (hℓ : ℓ ≤ m)
    (B : Matrix (Fin m) (Fin n) (ZMod 2)) (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) :
    ∀ u : Fin (ℓ + 1) → ℝ,
      |u ⬝ᵥ (Emat B dec ℓ).mulVec u| ≤
        2 * epsMax B dec ℓ * ((m : ℝ) + 1) * (u ⬝ᵥ u) := by sorry

end DQI.Imperfect
