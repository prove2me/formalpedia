-- Prove2me | Theorems.Thm_ConstDepthUnitary_fHat_wSamp
-- name    : ConstDepthUnitary.fHat_wSamp
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:47:43.831296+00:00
-- url     : https://prove2.me/theorems/66a9da22-fc86-4b3a-aa5d-4e906f5f8c27
-- title:
--   Lemma 5.3 — the discrete Fourier transform intertwines wrapped sampling
-- statement:
--   Let $K>0$ be even, and let $\psi$ be a Schwartz function on $\mathbb R^N$. Then the wrapped sums converge at every grid point, and
--   $$\hat F\,\mathrm{WSamp}_{\Lambda^N}|\psi\rangle=\mathrm{WSamp}_{\Lambda^N}F|\psi\rangle.$$
--   Thus wrapped sampling turns the continuous Fourier transform $F$ into the discrete one $\hat F$ with no error, for functions of arbitrary norm.
--
--   Differences from the source:
--   - generalization: K = 2^k, and |ψ⟩ a state in S(ℝ^N) → any positive even K and any Schwartz function, normalized or not; reason: footnote 15 says only evenness is used; §5.2.4 applies the lemma to un-normalized functions; both specialize to the printed case
--   - encoding: Eq. (63) as an identity of vectors, sums implicit → pointwise in w, with summability of both wrapped sums in the conclusion; reason: a Lean infinite sum of a non-summable family is 0
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 5.3, Eq. (63), p.28

import Mathlib
import Definitions.Def_ConstDepthUnitary_FHat
import Definitions.Def_ConstDepthUnitary_contF
import Definitions.Def_ConstDepthUnitary_sampShift
open scoped SchwartzMap

namespace ConstDepthUnitary

/-- Lemma 5.3: for `ψ` in the Schwartz space `S(ℝ^N)`, `F̂ WSamp_{Λ^N} |ψ⟩ = WSamp_{Λ^N} F |ψ⟩`, Eq. (63), with
both wrapped sums convergent at every grid point.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 5.3, p.28.

**Formalization Note** `K` is any positive even integer (the paper's `K = 2^k` is even, footnote 15, and only evenness
is used, pp.28–29), and `ψ` any Schwartz function, normalized or not (§5.2.4 applies the lemma to un-normalized states). -/
theorem fHat_wSamp {N K : ℕ} (hK : Even K) (hK0 : 0 < K) (ψ : 𝓢(EuclideanSpace ℝ (Fin N), ℂ)) :
    (∀ w : Fin N → Fin K, Summable fun m : Fin N → ℤ => (-1 : ℂ) ^ (∑ j, m j) * sampShift K m ψ w) ∧
    (∀ w : Fin N → Fin K, Summable fun m : Fin N → ℤ =>
      (-1 : ℂ) ^ (∑ j, m j) * sampShift K m (contF ψ) w) ∧
    ∀ w : Fin N → Fin K, (FHat N K).mulVec (wSamp K ψ) w = wSamp K (contF ψ) w := by sorry

end ConstDepthUnitary
