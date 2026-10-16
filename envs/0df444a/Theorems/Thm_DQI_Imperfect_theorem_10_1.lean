-- Prove2me | Theorems.Thm_DQI_Imperfect_theorem_10_1
-- name    : DQI.Imperfect.theorem_10_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:03:16.531+00:00
-- url     : https://prove2.me/theorems/6c8d22ff-aebc-4a0d-b6e6-0ee27259a3a6
-- title:
--   Theorem 10.1 — first imperfect-decoding bound
-- statement:
--   Let $B\in\mathbb F_2^{m\times n}$ define a max-XORSAT objective $f_v(x)=\sum_{i=1}^m(-1)^{b_i\cdot x+v_i}$. Fix $\ell\le m$, real weights $w_0,\ldots,w_\ell$, and one deterministic decoder of syndromes $B^\top y$. Let $F_k$ be its misidentified errors of weight $k$, $\varepsilon_k=|F_k|/\binom m k$, $\varepsilon=\max_{0\le k\le\ell}\varepsilon_k$, and $N=\sum_{k=0}^{\ell}w_k^2(1-\varepsilon_k)>0$. Prepare the postselected state (171), apply the binary Hadamard transform, normalize, and measure a binary string. If $v$ is uniform in $\mathbb F_2^m$, then the expected measured objective obeys
--
--   $$
--   \mathbb E_v\langle f_v\rangle\ge
--   \frac{w^\top A^{(m,\ell,0)}w-2\varepsilon(m+1)w^\top w}{N}.
--   $$
--
--   The bound quantifies the objective loss from imperfect decoding without assuming a minimum dual-code distance.
--
--   **Formalization Note** This is the first inequality of (172). The printed second inequality is false without a sign condition and is a separate companion item. The conditions $\ell\le m$ and $N>0$ ensure that the shell normalizations and measured-state expectation have their intended meanings. The decoder is fixed independently of $v$.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, pp. 39–40, Theorem 10.1, (172), first inequality

import Mathlib
import Definitions.Def_DQI_Imperfect_Setting

namespace DQI.Imperfect

theorem theorem_10_1 (m n ℓ : ℕ) (hℓ : ℓ ≤ m)
    (B : Matrix (Fin m) (Fin n) (ZMod 2)) (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (w : Fin (ℓ + 1) → ℝ)
    (hN : 0 < (∑ k, (w k) ^ 2 * (1 - epsk B dec k.val))) :
    ((w ⬝ᵥ (DQI.Semicircle.Atri m ℓ 0).mulVec w) -
        2 * epsMax B dec ℓ * ((m : ℝ) + 1) * (w ⬝ᵥ w)) /
      (∑ k, (w k) ^ 2 * (1 - epsk B dec k.val)) ≤
      avgV m (fun v => expObj B v (hadamard (PtD B v dec ℓ w))) := by sorry

end DQI.Imperfect
