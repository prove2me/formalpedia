-- Prove2me | Theorems.Thm_DQI_Imperfect_lemma_10_2
-- name    : DQI.Imperfect.lemma_10_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:03:21.388914+00:00
-- url     : https://prove2.me/theorems/eceae325-8ae2-4f09-95b2-2be53c7356a7
-- title:
--   Lemma 10.2 — objective matrix of the ideal state
-- statement:
--   For the binary max-XORSAT instance $(B,v)$, take the Hadamard transform of the ideal syndrome state $\widetilde P(f)$ in (140), with weights $w_0,\ldots,w_\ell$. If the resulting state is normalized, its measured objective expectation is
--
--   $$
--   \langle f\rangle=w^\top\bar A^{(m,\ell)}w,
--   $$
--
--   where $\bar A^{(m,\ell)}$ is the symmetric matrix of (147): its $(k,k')$ entry sums $(-1)^{v_i+v\cdot(y+y')}$ over the pairs $|y|=k$, $|y'|=k'$ for which $B^\top(y+y'+e_i)=0$, divided by $\sqrt{\binom m k\binom m{k'}}$. This expresses the observable in the weight basis, including collisions of syndrome values.
--
--   **Formalization Note** The normalized-state hypothesis is the equality of the transformed state's squared norm to one; $\ell\le m$ keeps its shell denominators nonzero.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 36, Lemma 10.2, (146)–(148)

import Mathlib
import Definitions.Def_DQI_Imperfect_Setting

namespace DQI.Imperfect

theorem lemma_10_2 (m n ℓ : ℕ) (hℓ : ℓ ≤ m)
    (B : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2) (w : Fin (ℓ + 1) → ℝ)
    (hnorm : (∑ x, (hadamard (Pt B v ℓ w) x) ^ 2) = 1) :
    expObj B v (hadamard (Pt B v ℓ w)) =
      w ⬝ᵥ (Abar B v ℓ).mulVec w := by sorry

end DQI.Imperfect
