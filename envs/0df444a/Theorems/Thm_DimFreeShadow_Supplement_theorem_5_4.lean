-- Prove2me | Theorems.Thm_DimFreeShadow_Supplement_theorem_5_4
-- name    : DimFreeShadow.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:02:50.833581+00:00
-- url     : https://prove2.me/theorems/5a2c9149-679e-4b4f-91b2-710da5334372
-- title:
--   Theorem 5.4 — a grid POVM good on a trace-distance $s$-net is good on every state
-- statement:
--   Let $E_1,\dots,E_M$ be effects on a finite-dimensional Hilbert space $\mathcal H$, write $\vartheta(\rho)=(\operatorname{Tr}(E_j\rho))_{j}$, and let $T$ be a positive integer. For an accuracy $\epsilon$ let $\mathcal Z_\epsilon=\{k/K_\epsilon:0\le k\le K_\epsilon\}^M$ with $K_\epsilon=\lceil2/\epsilon\rceil$. For a $\mathcal Z_\epsilon$-outcome POVM $N=(N_z)$ on $\mathcal H^{\otimes T}$, a state $\rho$ and a tolerance $a$, put
--
--   $$
--   f_{\rho,a}(N)=\sum_{z:\ \|z-\vartheta(\rho)\|_\infty>a}\operatorname{Tr}(N_z\rho^{\otimes T}),
--   $$
--
--   the failure probability of $N$ with the identity decoder. A **finite trace-distance $s$-net** is a finite set $F_s$ of states such that every state $\rho$ has some $\sigma\in F_s$ with $d_{\mathrm{tr}}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1\le s$.
--
--   **Theorem.** Let $0<\epsilon<\varepsilon\le1$ and $0<\beta<\delta<1$, and choose $0<s\le\min\{\varepsilon-\epsilon,(\delta-\beta)/T\}$. If a $\mathcal Z_\epsilon$-outcome POVM $N$ satisfies $\max_{\sigma\in F_s}f_{\sigma,\epsilon}(N)\le\beta$ on a finite trace-distance $s$-net $F_s$, then
--
--   $$
--   \sup_{\rho\in D(\mathcal H)}f_{\rho,\varepsilon}(N)\le\delta .
--   $$
--
--   This is the step that lifts the finite-family minimax guarantee to all states; the size of the net, and hence the dimension, does not enter the copy count.
--
--   **Formalization Note** $f_{\rho,a}(N)$ is the published `failureProb E N gridValue a ρ` with the published grid `Grid M ϵ`, and $d_{\mathrm{tr}}$ is the published `traceDistance`. The net is a `Finset` of density matrices with the covering property; "max" and "sup" are stated pointwise.
--
--   Differences from the source:
--   - encoding: a finite-dimensional Hilbert space H and its tensor powers → ℂ^d for a finite type d, with H^{⊗T} indexed by Fin T → d; reason: every finite-dimensional Hilbert space is unitarily equivalent to some ℂ^d; the same instances
--   - encoding: max_{σ∈F_s} f_{σ,ϵ}(N) ≤ β and sup_ρ f_{ρ,ε}(N) ≤ δ → f_{σ,ϵ}(N) ≤ β for every σ ∈ F_s and f_{ρ,ε}(N) ≤ δ for every density matrix ρ; reason: a max or sup is at most a bound exactly when every term is
--   - encoding: ‖z − ϑ(ρ)‖_∞ > a → ∃ j, a < |z_j − Tr(E_jρ)|; reason: the same event
--   - generalization: M ≥ 1 observables (standing hypothesis of Theorem 1.2) → any M, including M = 0; reason: at M = 0 every failure probability is 0, so the Lean statement specializes to the source's at M ≥ 1
--   - encoding: Tr(·) of an effect times a state (a real number) → the real part .re of the complex trace; reason: the trace of a product of two positive semidefinite matrices is real; the same value
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Theorem 5.4, Eq. (28), p.24; grid §5.1, p.20; f_{ρ,a} and positive T §5.2, p.21; s-net §5.3, p.23

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_DimFreeShadow_IsShadowStrategy
import Definitions.Def_DimFreeShadow_gridValue
import Definitions.Def_DimFreeShadow_traceDistance

namespace DimFreeShadow

namespace Supplement

/-- **Theorem 5.4 (net extension)** (arXiv:2608.06345, sha256 a1a42249…, Theorem 5.4, Eq. (28),
p.24; setting §5.1–5.3, pp.20–23). Let `0 < ϵ < ε ≤ 1` and `0 < β < δ < 1`. Fix `T`, and choose
`0 < s ≤ min{ε − ϵ, (δ − β)/T}`. If a `Z_ϵ`-outcome POVM `N` satisfies
`max_{σ∈F_s} f_{σ,ϵ}(N) ≤ β` on a finite trace-distance s-net `F_s`, then
`sup_{ρ∈D(H)} f_{ρ,ε}(N) ≤ δ` (28).

**Formalization Note** `H = ℂ^d` for a finite type `d`; the effects are `E_1, …, E_M`
(`Fin M`). `T` is a positive integer ("Fix a positive integer T", p.21). `N` is a POVM on
`H^{⊗T}` with outcome type the published grid `Grid M ϵ` (`K_ϵ = ⌈2/ϵ⌉`), and
`f_{ρ,a}(N) = Σ_{z : ‖z − ϑ(ρ)‖_∞ > a} Tr(N_z ρ^{⊗T})` is the published
`failureProb E N gridValue a ρ` (identity decoder `g(z) = z`, p.21). A finite trace-distance
s-net is a `Finset` of density matrices such that every density matrix `ρ` has a member `σ` with
`d_tr(ρ, σ) ≤ s` (p.23). "`max ≤ β`" and "`sup ≤ δ`" are stated pointwise. -/
theorem theorem_5_4 {d : Type} [Fintype d] [DecidableEq d] {M : ℕ} (E : Fin M → Matrix d d ℂ)
    (hE : ∀ j, QAlgorithms.IsEffect (E j)) (ϵ ε β δ : ℝ) (hϵ : 0 < ϵ) (hϵε : ϵ < ε)
    (hε1 : ε ≤ 1) (hβ : 0 < β) (hβδ : β < δ) (hδ1 : δ < 1) (T : ℕ) (hT : 1 ≤ T) (s : ℝ)
    (hs0 : 0 < s) (hs1 : s ≤ ε - ϵ) (hs2 : s ≤ (δ - β) / T)
    (Fs : Finset (Matrix d d ℂ)) (hFs : ∀ σ ∈ Fs, WildeQIT.IsDensityOperator σ)
    (hnet : ∀ ρ : Matrix d d ℂ, WildeQIT.IsDensityOperator ρ →
      ∃ σ ∈ Fs, traceDistance ρ σ ≤ s)
    (N : Grid M ϵ → Matrix (Fin T → d) (Fin T → d) ℂ) (hN : QAlgorithms.IsPOVM N)
    (hNβ : ∀ σ ∈ Fs, failureProb E N gridValue ϵ σ ≤ β) :
    ∀ ρ : Matrix d d ℂ, WildeQIT.IsDensityOperator ρ →
      failureProb E N gridValue ε ρ ≤ δ := by sorry

end Supplement

end DimFreeShadow
