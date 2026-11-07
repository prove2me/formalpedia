-- Prove2me | Theorems.Thm_ConstDepthUnitary_sampling_commutator_le
-- name    : ConstDepthUnitary.sampling_commutator_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:47:52.041797+00:00
-- url     : https://prove2.me/theorems/194af201-340f-4eb6-961a-47445f9518d6
-- title:
--   Corollary 5.6 — the sampling commutator is bounded by the out-of-grid tails
-- statement:
--   Let $K>0$ be even and $\psi$ a Schwartz function on $\mathbb R^N$. Then the two series below converge, and in the Euclidean norm on $\mathbb C^{[K]^N}$
--   $$\bigl\|\hat F\,\mathrm{Samp}_{\Lambda^N}|\psi\rangle-\mathrm{Samp}_{\Lambda^N}F|\psi\rangle\bigr\|\le\sum_{m\in\mathbb Z^N\setminus\{0\}}\bigl\|\mathrm{Samp}^{(m)}_{\Lambda^N}F|\psi\rangle\bigr\|+\sum_{m\in\mathbb Z^N\setminus\{0\}}\bigl\|\mathrm{Samp}^{(m)}_{\Lambda^N}|\psi\rangle\bigr\|.$$
--   The difference between applying the discrete transform after sampling and the continuous one before sampling is controlled by the weight outside the grid on both sides.
--
--   Differences from the source:
--   - generalization: K = 2^k, and |ψ⟩ a state in S(ℝ^N) → any positive even K and any Schwartz function; reason: as in Lemma 5.3; it specializes to the printed case
--   - encoding: the series without a convergence clause → summability of both series in the conclusion; reason: a Lean infinite sum of a non-summable family is 0
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Corollary 5.6, Eq. (68), p.30

import Mathlib
import Definitions.Def_ConstDepthUnitary_FHat
import Definitions.Def_ConstDepthUnitary_contF
import Definitions.Def_ConstDepthUnitary_sampShift
open scoped SchwartzMap

namespace ConstDepthUnitary

/-- Corollary 5.6, Eq. (68): `‖F̂ Samp_{Λ^N} |ψ⟩ − Samp_{Λ^N} F |ψ⟩‖ ≤ Σ_{m ≠ 0} ‖Samp^{(m)}_{Λ^N} F |ψ⟩‖ +
Σ_{m ≠ 0} ‖Samp^{(m)}_{Λ^N} |ψ⟩‖`, with both series convergent. The norm is the Euclidean norm on `ℂ^{[K]^N}`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Corollary 5.6, p.30.

**Formalization Note** As in `fHat_wSamp`: `K` positive even, `ψ` any Schwartz function. -/
theorem sampling_commutator_le {N K : ℕ} (hK : Even K) (hK0 : 0 < K)
    (ψ : 𝓢(EuclideanSpace ℝ (Fin N), ℂ)) :
    Summable (fun m : {m : Fin N → ℤ // m ≠ 0} => l2Norm (sampShift K m.1 (contF ψ))) ∧
    Summable (fun m : {m : Fin N → ℤ // m ≠ 0} => l2Norm (sampShift K m.1 ψ)) ∧
    l2Norm ((FHat N K).mulVec (sampShift K 0 ψ) - sampShift K 0 (contF ψ)) ≤
      ∑' m : {m : Fin N → ℤ // m ≠ 0}, l2Norm (sampShift K m.1 (contF ψ)) +
        ∑' m : {m : Fin N → ℤ // m ≠ 0}, l2Norm (sampShift K m.1 ψ) := by sorry

end ConstDepthUnitary
