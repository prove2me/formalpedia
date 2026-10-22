-- Prove2me | Theorems.Thm_DQI_Imperfect_lemma_10_5
-- name    : DQI.Imperfect.lemma_10_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:03:28.444572+00:00
-- url     : https://prove2.me/theorems/3cc58cf8-d1cd-4f44-b6cb-14e64fac37e3
-- title:
--   Lemma 10.5 — objective matrix after imperfect decoding
-- statement:
--   Let $D_k$ be the weight-$k$ errors correctly recovered by a deterministic decoder of $B^\top y$. For the normalized Hadamard transform of the postselected state $\widetilde P_D(f)$, the expected max-XORSAT objective is
--
--   $$
--   \langle f\rangle=w^\top\bar A^{(m,\ell,D)}w.
--   $$
--
--   The $(k,k')$ entry of $\bar A^{(m,\ell,D)}$ is the sum of $(-1)^{v_i+v\cdot(y+y')}$ over $i$ and $(y,y')\in D_k\times D_{k'}$ with $B^\top(y+y'+e_i)=0$, divided by $\sqrt{\binom m k\binom m{k'}}$. This is the objective matrix for the retained, correctly decoded errors.
--
--   **Formalization Note** The hypothesis that the transformed state has squared norm one states the paper's normalization condition. The formalization assumes $\ell\le m$.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, pp. 40–41, Lemma 10.5, (176)–(178)

import Mathlib
import Definitions.Def_DQI_Imperfect_Setting

namespace DQI.Imperfect

theorem lemma_10_5 (m n ℓ : ℕ) (hℓ : ℓ ≤ m)
    (B : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2) (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (w : Fin (ℓ + 1) → ℝ)
    (hnorm : (∑ x, (hadamard (PtD B v dec ℓ w) x) ^ 2) = 1) :
    expObj B v (hadamard (PtD B v dec ℓ w)) =
      w ⬝ᵥ (AbarD B v dec ℓ).mulVec w := by sorry

end DQI.Imperfect
