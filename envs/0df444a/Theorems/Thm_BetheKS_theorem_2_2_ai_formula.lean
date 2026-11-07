-- Prove2me | Theorems.Thm_BetheKS_theorem_2_2_ai_formula
-- name    : BetheKS.theorem_2_2_ai_formula
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:32.77278+00:00
-- url     : https://prove2.me/theorems/fb6c98c2-c0b4-4801-b4c9-43723fdd0d9d
-- title:
--   Proof of Theorem 2.2 ($a_i>0$), p.12 — the formula for $a_i=\mathbb E[V_i(o)X_i(o)]$
-- statement:
--   Take $t=\sqrt d$. For an informative eigenvalue $\mu_i$ of either sign, write $\delta_i=\delta(|\mu_i|)$, and let $\Gamma_i$ and $h_i$ be the positive cavity weight and the transfer eigenfunction (Proposition 4.4) at this shift. If $K$ is the root degree and $T_1,\dots,T_K$ are its forward subtrees, taking conditional expectations in the vertex-field formula gives
--   $$
--   a_i=\frac{t|\mu_i|}{d}\,\mathbb E\left[\frac{\sum_{j=1}^Kh_i(T_j)}{t^2+K-1+\delta_i-t\sum_{j=1}^K\Gamma_i(T_j)}\right]>0,
--   $$
--   where $a_i=\mathbb E[V_i(o)X_i(o)]$, $V_i$ the vertex field of $\mu_i$ (with $-\Gamma$, $-t$ for negative $\mu_i$) and $X_i(o)=\phi_i(\sigma(o))$. The positivity gives $c_\mu>0$ and $q_{\mu}>0$ in Theorem 2.2.
--
--   **Formalization Note** $h_i$ is normalized as in Proposition 4.4 (the $L^2$ limit of $\kappa^{-L}\mathcal L^L\mathbf 1$) and read through its real part; $\phi_i$ satisfies $Q\phi_i=\mu_i\phi_i$, $\sum_a\pi_a\phi_i(a)^2=1$. Both the equality and the strict positivity are asserted.
--
--   Differences from the source:
--
--   - encoding: the multitype Galton–Watson tree ν̃ of Definition 5.1 → the Poi(d) tree with labels broadcast by the kernel Q_{ij}/d from a π-distributed root; reason: Poisson thinning with Σ_j Q_ij = d gives Poi(Q_ij) children of type j independently over j: the same law (children ordered)
--   - encoding: Ω the locally finite rooted trees, ν the Poi(d) Galton–Watson law → offspring functions on Ulam–Harris words (children ordered) with i.i.d. Poi(d) coordinates; reason: the tree read off has law ν and, given the root degree, the forward subtrees are i.i.d. ν, which is all the arguments use; κ, h, δ(μ) are unchanged
--   - encoding: π a distribution on [r] → every π_a > 0; reason: the r eigenfunctions orthonormal in L²(π) that the paper uses exist only then; excludes undefined cases
--   - encoding: μ_i an informative eigenvalue of either sign with eigenfunction ϕ_i → s ∈ {±1}, √d < sμ, Qϕ = μϕ, Σ_a π_a ϕ(a)² = 1, δ_i := deltaOf d √d |μ|; reason: the proof's setting
--   - reading: h_i, the transfer eigenfunction at the shift δ_i → hFun, the L² limit of κ^{−L}ℒ^L 1 (the h of Proposition 4.4 (4)), through its real part; reason: the conditional-mean identity E[b^{(L)}_u | T₀, σ(u)] = ρ^L ℒ^L 1(T_u) X_u (p.9) converges to this h, which fixes the normalization the formula needs; Proposition 4.4 (1) alone fixes h only up to a positive factor
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Proof of Theorem 2.2, p.12 (PDF p.13), display "a_i = …"

import Mathlib
import Definitions.Def_BetheKS_treeVertexField
import Definitions.Def_BetheKS_transferOp

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace BetheKS

open Classical

/-- **Proof of Theorem 2.2 (`aᵢ > 0`)** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256
4da41e16…), p.12 (PDF p.13): at `t = √d`, for either sign write `δᵢ = δ(|µᵢ|)` and let `Γᵢ`, `hᵢ` be
the positive cavity weight and transfer eigenfunction at this shift. If `K` is the root degree and
`T₁,…,T_K` are its forward subtrees, then
`aᵢ = (t|µᵢ|/d) E[∑_{j=1}^K hᵢ(Tⱼ) / (t² + K − 1 + δᵢ − t ∑_{j=1}^K Γᵢ(Tⱼ))] > 0`,
where `aᵢ := E[Vᵢ(o) Xᵢ(o)]` (Proposition 7.1).

**Formalization Note.** `s = 1` for a positive informative `µᵢ` and `s = −1` for a negative one; `Vᵢ`
is the vertex field of sign `s` (`−Γ`, `−t` in the messages and the numerator, p.12) built from
`ϕᵢ` with `Q ϕᵢ = µᵢ ϕᵢ`, `∑ₐ πₐ ϕᵢ(a)² = 1`. `hᵢ` is the eigenfunction of Proposition 4.4 normalized
as there (the `L²` limit of `κ^{−L}ℒ^L1`), read through its real part; `Γᵢ` is the root cavity weight
of Definition A.1. Both the equality and the strict positivity are asserted. -/
theorem theorem_2_2_ai_formula {r : ℕ} (p : SBMParams r) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (μ : ℝ) (hμ : Real.sqrt p.d < s * μ)
    (ϕ : Fin r → ℝ) (hϕ : (signal p).mulVec ϕ = μ • ϕ) (hϕn : ∑ a, p.pi a * ϕ a ^ 2 = 1) :
    (∫ ω, Vtree p ϕ s (Real.sqrt p.d) (deltaOf p.d (Real.sqrt p.d) |μ|) [] ω * ϕ (label ω [])
        ∂mgwLaw p) =
      Real.sqrt p.d * |μ| / p.d *
        ∫ ω, (∑ j ∈ Finset.range (ω.1 []),
            ((hFun p.d (Real.sqrt p.d) (deltaOf p.d (Real.sqrt p.d) |μ|) : Offspring → ℂ)
              (subtree ω.1 j)).re) /
          (Real.sqrt p.d ^ 2 + (ω.1 [] : ℝ) - 1 + deltaOf p.d (Real.sqrt p.d) |μ| -
            Real.sqrt p.d * ∑ j ∈ Finset.range (ω.1 []),
              treeGamma (Real.sqrt p.d) (deltaOf p.d (Real.sqrt p.d) |μ|) (subtree ω.1 j)) ∂mgwLaw p ∧
    0 < ∫ ω, Vtree p ϕ s (Real.sqrt p.d) (deltaOf p.d (Real.sqrt p.d) |μ|) [] ω * ϕ (label ω [])
        ∂mgwLaw p := by sorry

end BetheKS
