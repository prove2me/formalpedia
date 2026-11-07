-- Prove2me | Theorems.Thm_ConstDepthUnitary_gammaHat_sub_gammaTilde_le
-- name    : ConstDepthUnitary.gammaHat_sub_gammaTilde_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:49:56.251663+00:00
-- url     : https://prove2.me/theorems/01000211-3a1f-46ef-abb5-af1c50719618
-- title:
--   Lemma 5.2 — the half-algorithm is close to the ideal isometry
-- statement:
--   There is a universal constant $C$ such that for all $N$, every positive even $K$ and every traceless real symmetric unitary $S$ on $\mathbb C^N$,
--   $$\bigl\|\hat\Gamma_S-\tilde\Gamma_S\bigr\|\le C\,N^{3/2}K^{3/4}e^{-\pi K/8}$$
--   in operator norm.
--
--   Differences from the source:
--   - encoding: constants hidden in O(·) → an existential constant quantified before all data; reason: the paper's constants are universal
--   - generalization: K = 2^k → any positive even K; reason: footnote 15: evenness is what the proof uses; it specializes to the printed case
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 5.2, Eq. (59), p.27

import Mathlib
import Definitions.Def_ConstDepthUnitary_IsTRS
import Definitions.Def_ConstDepthUnitary_GammaHat
import Definitions.Def_ConstDepthUnitary_GammaTilde
open scoped Matrix.Norms.L2Operator

namespace ConstDepthUnitary

/-- Lemma 5.2, Eq. (59): `‖Γ̂_S − Γ̃_S‖ ≤ O(N^{3/2} K^{3/4} e^{−πK/8})`, with a universal constant, for every traceless
real symmetric unitary `S` and positive even `K`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 5.2, p.27. -/
theorem gammaHat_sub_gammaTilde_le :
    ∃ C : ℝ, ∀ (N K : ℕ) (S : Matrix (Fin N) (Fin N) ℝ), Even K → 0 < K → IsTRS S →
      ‖GammaHat K S - GammaTilde K S‖ ≤
        C * (N : ℝ) ^ (3 / 2 : ℝ) * (K : ℝ) ^ (3 / 4 : ℝ) * Real.exp (-Real.pi * K / 8) := by sorry

end ConstDepthUnitary
