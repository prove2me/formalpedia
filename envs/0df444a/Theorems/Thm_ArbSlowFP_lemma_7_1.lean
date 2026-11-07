-- Prove2me | Theorems.Thm_ArbSlowFP_lemma_7_1
-- name    : ArbSlowFP.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:46:47.323021+00:00
-- url     : https://prove2.me/theorems/cad22a46-c5d0-4743-a5d3-59028bb5af33
-- title:
--   Lemma 7.1 — all linear compatibility tests for $L$
-- statement:
--   For $k\ge2$, the matrices $Z^{(h)}_{DP}$ of $(29)$, for even $h\in[k,2k]$, form a basis of the kernel of $L^*_{DP}(Z)=Z-e^{-N_0}Z^\top$. In binomial coordinates, the corresponding basis is $Z^{(h)}=S_wZ^{(h)}_{DP}S_w^\top$, a basis of the kernel of the adjoint $L^*(Z)=Z-BZ^\top$ of $L$. Consequently, $L(E)=F$ is solvable over $\mathbb Q$ if and only if $\langle Z^{(h)},F\rangle=0$ for every even integer $h\in[k,2k]$.
--
--   **Formalization Note** Being a basis is stated as linear independence over the index subtype together with: a matrix lies in the kernel if and only if it lies in the span.
--
--   Differences from the source:
--   - reading: "In binomial coordinates, the corresponding basis" → a basis of the kernel of Z ↦ Z − BZ⊤; reason: p.43 gives L*(Z) = Z − BZ⊤ as the adjoint in binomial coordinates, and the proof derives the kernel from it
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.44, Lemma 7.1

import Mathlib
import Definitions.Def_ArbSlowFP_binomBasis

open Matrix

namespace ArbSlowFP

/-- Lemma 7.1, p.44 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…). For `k ≥ 2`, the
matrices `Z^(h)_DP` of (29), for even `h ∈ [k, 2k]`, form a basis of the kernel of
`L∗_DP(Z) = Z - e^{-N₀}Z⊤`. In binomial coordinates, `Z^(h) = S_w Z^(h)_DP S_w⊤` form a basis of the kernel
of the adjoint `L∗(Z) = Z - BZ⊤` of `L`. Consequently, `L(E) = F` is solvable over `ℚ` if and only if
`⟨Z^(h), F⟩ = 0` for every even integer `h ∈ [k, 2k]`.

**Formalization Note.** A basis is stated as linear independence over the index subtype together with:
`Z` lies in the kernel if and only if it lies in the span. -/
theorem lemma_7_1 (k : ℕ) (hk : 2 ≤ k) :
    let Idx := {h : ℕ // Even h ∧ k ≤ h ∧ h ≤ 2 * k}
    LinearIndependent ℚ (fun h : Idx => testZDP k h.1) ∧
    (∀ Z : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ,
      Z - expN0 (k + 1) (-1) * Zᵀ = 0 ↔
        Z ∈ Submodule.span ℚ (Set.range fun h : Idx => testZDP k h.1)) ∧
    LinearIndependent ℚ (fun h : Idx => testZ k h.1) ∧
    (∀ Z : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ,
      Z - shiftB (k + 1) * Zᵀ = 0 ↔
        Z ∈ Submodule.span ℚ (Set.range fun h : Idx => testZ k h.1)) ∧
    ∀ F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ,
      (∃ E, opL E = F) ↔ ∀ h, Even h → k ≤ h → h ≤ 2 * k → frob (testZ k h) F = 0 := by sorry

end ArbSlowFP
