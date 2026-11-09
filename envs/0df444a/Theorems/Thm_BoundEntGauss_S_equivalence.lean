-- Prove2me | Theorems.Thm_BoundEntGauss_S_equivalence
-- name    : BoundEntGauss.S_equivalence
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:49:34.887776+00:00
-- url     : https://prove2.me/theorems/ad8597c5-c15e-4e33-8a9d-4c9b0553fb3d
-- title:
--   Section IV — $S\sigma+\tilde\sigma S=0$ and $\gamma-i\tilde\sigma=S(\gamma+i\sigma)S$ for every $\gamma$ commuting with $S$
-- statement:
--   On the $2\times2$-mode phase space, let $S=\operatorname{diag}(1,1,-1,-1,1,-1,-1,1)$. Then
--
--   1. $S\sigma+\tilde\sigma S=0$;
--   2. for every real $8\times8$ matrix $\gamma$ with $S\gamma=\gamma S$,
--   $$
--   \gamma-i\tilde\sigma=S(\gamma+i\sigma)S .
--   $$
--
--   Since $S$ is real orthogonal, $\gamma+i\sigma$ and $\gamma-i\tilde\sigma$ are unitarily equivalent. Hence for such $\gamma$ the condition $\gamma+i\tilde\sigma\ge0$ (equivalently $\gamma-i\tilde\sigma\ge0$) follows from $\gamma+i\sigma\ge0$, so a covariance of the family is a ppt-covariance as soon as it is a covariance.
--
--   Differences from the source:
--   - generalization: the identity for the covariance matrix of the example (9) (and the family (11)), which commutes with S → the identity for every real γ with Sγ = γS; reason: the paper's "Consequently" uses only Sγ = γS; specializing γ to (9) or to γ(a,b,c,e,f) gives the printed claim
--   - encoding: "γ + iσ and γ − iσ̃ = S(γ + iσ)S are unitarily equivalent" → the matrix identity γ − iσ̃ = S(γ + iσ)S; reason: S is real orthogonal (S² = 1), so the identity is the unitary equivalence
--   - encoding: f canonical degrees of freedom, X = X_A ⊕ X_B, canonical coordinates → QuadratureIndex n ⊕ QuadratureIndex m (interleaved (x_j, p_j), Alice = Sum.inl), Fock space indexed by Occupation (Fin n) × Occupation (Fin m), for all n, m; reason: Lean representation of the same objects
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section IV, p. 4

import Mathlib
import Definitions.Def_BoundEntGauss_totalSigma
import Definitions.Def_BoundEntGauss_sigmaTilde
import Definitions.Def_BoundEntGauss_opS

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace BoundEntGauss

/-- **The symmetry S intertwines γ + iσ and γ − iσ̃.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section IV, p. 4: "The most important symmetry in the example is the multiplication operator S
with diagonal matrix elements (1, 1, −1, −1, 1, −1, −1, 1). It satisfies Sσ + σ̃S = 0, and Sγ = γS.
Consequently, γ + iσ and γ − iσ̃ = S(γ + iσ)S are unitarily equivalent".

1. `S σ + σ̃ S = 0` for the `2 × 2`-mode `σ` and `σ̃`.
2. For every real `8 × 8` matrix `γ` with `S γ = γ S`: `γ − iσ̃ = S (γ + iσ) S`.

**Formalization Note.** Part 2 is stated for every `γ` commuting with `S`, the hypothesis the
paper's "Consequently" uses; it covers the example (9) and the family (11). -/
theorem S_equivalence :
    opS * totalSigma 2 2 + sigmaTilde 2 2 * opS = 0 ∧
    ∀ Γ : Matrix (QuadratureIndex 2 ⊕ QuadratureIndex 2) (QuadratureIndex 2 ⊕ QuadratureIndex 2) ℝ,
      opS * Γ = Γ * opS →
      complexify Γ - Complex.I • complexify (sigmaTilde 2 2) =
        complexify opS * (complexify Γ + Complex.I • complexify (totalSigma 2 2)) * complexify opS := by sorry

end BoundEntGauss
