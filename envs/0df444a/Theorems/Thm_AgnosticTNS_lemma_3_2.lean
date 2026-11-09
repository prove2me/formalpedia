-- Prove2me | Theorems.Thm_AgnosticTNS_lemma_3_2
-- name    : AgnosticTNS.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:34:23.144289+00:00
-- url     : https://prove2.me/theorems/6aedf045-072f-42f9-9811-c164f011d1e5
-- title:
--   Lemma 3.2 — top subspace from an approximate state
-- statement:
--   Let $\sigma\ge0$ be a subnormalised state ($\mathrm{tr}\,\sigma\le1$) on a $D$-dimensional Hilbert space and $\hat\sigma\ge0$ with $\|\sigma-\hat\sigma\|_\infty\le\gamma$. Let $W$ be the span of the eigenvectors of $\hat\sigma$ for its $\Lambda$ largest eigenvalues and $Q=I-\Pi_W$. If $1\le\Lambda<D$, then
--   $$
--   \|Q\sigma Q\|_\infty\le\frac{\mathrm{tr}(\sigma)}{\Lambda+1}+2\gamma\le\frac1{\Lambda+1}+2\gamma .
--   $$
--   If $\Lambda\ge D$, then $Q=0$ and the left-hand side is zero.
--
--   Keeping the leading eigenvectors of an estimate therefore controls the discarded part of the true state, as required by Lemma 3.1.
--
--   Differences from the source:
--   - encoding: $D$-dimensional space, $\Pi_W$, $\|\cdot\|_\infty$ → basis `α` with $|\alpha|=D$, any matrix $P$ with $P^2=P=P^\dagger$ and range $W$, `opNorm`; reason: Lean convention; same instances
--   - reading: "the span of the eigenvectors associated with the $\Lambda$ largest eigenvalues of $\hat\sigma$" → the span of any $\min(\Lambda,D)$ orthonormal eigenvectors for the $\Lambda$ largest eigenvalues counted with multiplicity (`IsTopSpan`), every such choice; reason: ambiguous when eigenvalues are degenerate; this is the wording of Corollary 3.3, and every choice is covered
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Lemma 3.2, Eqs. (3.13)–(3.14), p.17

import Mathlib
import Definitions.Def_AgnosticTNS_opNorm
import Definitions.Def_AgnosticTNS_IsTopSpan
open Matrix
open scoped ComplexOrder

namespace AgnosticTNS

/-- **Lemma 3.2 (Top subspace from an approximate state)**, p.17 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). Let `σ ≥ 0` with
`tr σ ≤ 1` on a `D`-dimensional space and `σ̂ ≥ 0` with `‖σ − σ̂‖_∞ ≤ γ` (3.13). Let `W` be the span of
the eigenvectors of `σ̂` for its `Λ` largest eigenvalues and `Q = I − Π_W`. If `1 ≤ Λ < D` then
`‖QσQ‖_∞ ≤ tr(σ)/(Λ + 1) + 2γ ≤ 1/(Λ + 1) + 2γ` (3.14); if `Λ ≥ D` then `Q = 0` and the left-hand
side is zero.

**Formalization Note** `D = |α|`. "The eigenvectors associated with the `Λ` largest eigenvalues" is read
as in Corollary 3.3: any `Λ` orthonormal eigenvectors for the `Λ` largest eigenvalues counted with
multiplicity (`IsTopSpan`); every such choice is covered. `Π_W` is any matrix `P` with `P² = P = P†`
and range `W`. -/
theorem lemma_3_2 {α : Type} [Fintype α] [DecidableEq α] (σ σh : Matrix α α ℂ)
    (hσ : σ.PosSemidef) (htr : σ.trace.re ≤ 1) (hσh : σh.PosSemidef) (γ : ℝ)
    (hγ : opNorm (σ - σh) ≤ γ) (Λ : ℕ) (W : Submodule ℂ (α → ℂ)) (hW : IsTopSpan σh Λ W)
    (PW : Matrix α α ℂ) (hPW : PW * PW = PW) (hPWh : PWᴴ = PW)
    (hPWW : LinearMap.range PW.mulVecLin = W) :
    (1 ≤ Λ → Λ < Fintype.card α →
      opNorm ((1 - PW) * σ * (1 - PW)) ≤ σ.trace.re / (Λ + 1) + 2 * γ ∧
        σ.trace.re / (Λ + 1) + 2 * γ ≤ 1 / (Λ + 1) + 2 * γ) ∧
    (Fintype.card α ≤ Λ → 1 - PW = 0 ∧ opNorm ((1 - PW) * σ * (1 - PW)) = 0) := by sorry

end AgnosticTNS
