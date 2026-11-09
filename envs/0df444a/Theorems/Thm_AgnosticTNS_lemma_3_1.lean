-- Prove2me | Theorems.Thm_AgnosticTNS_lemma_3_1
-- name    : AgnosticTNS.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:34:17.828426+00:00
-- url     : https://prove2.me/theorems/2e414387-91c4-4105-9b8b-0b8431d5a72a
-- title:
--   Lemma 3.1 — agnostic projection bound
-- statement:
--   Let $\mathcal H_A,\mathcal H_B$ be finite-dimensional Hilbert spaces and $\rho\ge0$ a subnormalised state on $\mathcal H_A\otimes\mathcal H_B$ with $\mathrm{tr}(\rho)\le1$. Let $|\phi\rangle$ have $\|\phi\|\le1$ and Schmidt rank at most $r$ across $A\mid B$. Let $W\subseteq\mathcal H_A$, $\Pi_W$ the orthogonal projector onto $W$ and $Q=I_A-\Pi_W$. If $\|Q\,\mathrm{tr}_B(\rho)\,Q\|_\infty\le\eta$, then
--   $$
--   \big|\langle\phi|(\Pi_W\otimes I_B)\rho(\Pi_W\otimes I_B)|\phi\rangle-\langle\phi|\rho|\phi\rangle\big|\le2\sqrt{r\eta},
--   $$
--   and the same bound holds with $\Pi_W$ replaced by any orthogonal projector $\Pi$ on $\mathcal H_A$ whose range contains $W$.
--
--   Projecting one subsystem onto a subspace that captures the reduced state up to $\eta$ in operator norm changes the overlap with any low-Schmidt-rank reference vector by $O(\sqrt{r\eta})$, whatever the rank of $\rho$.
--
--   Differences from the source:
--   - encoding: $\mathcal H_A\otimes\mathcal H_B$, $\Pi\otimes I_B$, Schmidt rank, orthogonal projectors, $\|\cdot\|_\infty$, $\mathrm{tr}_B$ → bases `α × β`, `Matrix.kronecker P 1`, rank of the coefficient matrix $(a,b)\mapsto\phi(a,b)$, matrices with $P^2=P=P^\dagger$, `opNorm`, `WildeQIT.partialTraceRight`; reason: Lean convention; same instances
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Lemma 3.1, Eqs. (3.4)–(3.5), p.16

import Mathlib
import Definitions.Def_AgnosticTNS_expVal
import Definitions.Def_AgnosticTNS_opNorm
import Definitions.Def_WildeQIT_partialTrace
open Matrix
open scoped ComplexOrder

namespace AgnosticTNS

/-- **Lemma 3.1 (Agnostic projection bound)**, pp.16–17 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). Let `H_A, H_B` be finite-dimensional,
`ρ ≥ 0` on `H_A ⊗ H_B` with `tr ρ ≤ 1`, `|ϕ⟩` with `‖ϕ‖ ≤ 1` and Schmidt rank at most `r` across `A | B`,
`W ⊆ H_A`, `Π_W` the orthogonal projector onto `W` and `Q = I_A − Π_W`. If `‖Q tr_B(ρ) Q‖_∞ ≤ η`
(3.4), then `|⟨ϕ|(Π_W ⊗ I_B)ρ(Π_W ⊗ I_B)|ϕ⟩ − ⟨ϕ|ρ|ϕ⟩| ≤ 2√(rη)` (3.5), and the same holds with
`Π_W` replaced by any orthogonal projector `Π` on `H_A` whose range contains `W`.

**Formalization Note** `H_A ⊗ H_B` has basis `α × β`; `Π ⊗ I` is `Matrix.kronecker Π 1`; the Schmidt
rank of `ϕ` is the rank of its coefficient matrix `(a, b) ↦ ϕ(a, b)`; orthogonal projectors are
matrices `P` with `P² = P = P†`; `tr_B` is the published `WildeQIT.partialTraceRight`. -/
theorem lemma_3_1 {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : Matrix (α × β) (α × β) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1)
    (φ : α × β → ℂ) (hφ : ∑ x, ‖φ x‖ ^ 2 ≤ 1) (r : ℕ)
    (hr : (Matrix.of fun a b => φ (a, b)).rank ≤ r)
    (W : Submodule ℂ (α → ℂ)) (PW : Matrix α α ℂ) (hPW : PW * PW = PW) (hPWh : PWᴴ = PW)
    (hPWW : LinearMap.range PW.mulVecLin = W) (η : ℝ)
    (hη : opNorm ((1 - PW) * WildeQIT.partialTraceRight ρ * (1 - PW)) ≤ η) :
    |expVal (Matrix.kronecker PW (1 : Matrix β β ℂ) * ρ * Matrix.kronecker PW 1) φ - expVal ρ φ| ≤
        2 * Real.sqrt (r * η) ∧
      ∀ P : Matrix α α ℂ, P * P = P → Pᴴ = P → W ≤ LinearMap.range P.mulVecLin →
        |expVal (Matrix.kronecker P (1 : Matrix β β ℂ) * ρ * Matrix.kronecker P 1) φ - expVal ρ φ| ≤
          2 * Real.sqrt (r * η) := by sorry

end AgnosticTNS
