-- Prove2me | Theorems.Thm_BetheKS_lemma_D_5
-- name    : BetheKS.lemma_D_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:28.649807+00:00
-- url     : https://prove2.me/theorems/24b495d3-f66b-4617-990c-522f1bd4840a
-- title:
--   Lemma D.5 — $\mathbb E|V(o)|^2<\infty$ and $V^{(L)}(o)\to V(o)$ in $L^2$
-- statement:
--   On the labelled Galton–Watson tree $(T,o)\sim\widetilde\nu$, in the setting of §5 ($\mu>t\ge\sqrt d$ an eigenvalue of $Q$ with eigenfunction $\phi$, $\delta=\delta(\mu)$),
--   $$
--   \mathbb E|V(o)|^2<\infty\qquad\text{and}\qquad\mathbb E\big|V^{(L)}(o)-V(o)\big|^2\longrightarrow0\quad(L\to\infty).
--   $$
--
--   Differences from the source:
--
--   - encoding: §5 preamble: μ_i > t an eigenvalue of Q with eigenvector ϕ_i, δ = δ(μ_i) → hypotheses t ≥ √d, t < μ, Qϕ = μϕ, Σ_a π_a ϕ(a)² = 1, and δ := deltaOf d t μ; reason: the section's standing assumptions; the normalization is the paper's L²(π) convention
--   - encoding: convergence in L² → eLpNorm of the difference in L²(ν̃) tends to 0; reason: the definition of L² convergence; the norm is ℝ≥0∞-valued, so no integrability side condition hides in it
--   - encoding: the multitype Galton–Watson tree ν̃ of Definition 5.1 → the Poi(d) tree with labels broadcast by the kernel Q_{ij}/d from a π-distributed root; reason: Poisson thinning with Σ_j Q_ij = d gives Poi(Q_ij) children of type j independently over j: the same law (children ordered)
--   - encoding: Ω the locally finite rooted trees, ν the Poi(d) Galton–Watson law → offspring functions on Ulam–Harris words (children ordered) with i.i.d. Poi(d) coordinates; reason: the tree read off has law ν and, given the root degree, the forward subtrees are i.i.d. ν, which is all the arguments use; κ, h, δ(μ) are unchanged
--   - encoding: π a distribution on [r] → every π_a > 0; reason: the r eigenfunctions orthonormal in L²(π) that the paper uses exist only then; excludes undefined cases
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Lemma D.5, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_BetheKS_treeVertexField
import Definitions.Def_BetheKS_transferOp

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace BetheKS

open Classical

/-- **Lemma D.5** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), p.21
(PDF p.22): on the labeled Galton–Watson tree `(T, o)`, `E|V(o)|² < ∞` and
`E|V^{(L)}(o) − V(o)|² → 0` as `L → ∞`.

§5 preamble (p.8): `µ > t` is an eigenvalue of `Q` with eigenfunction `ϕ` (normalized in `L²(π)`), `ρ = µ/d`, `δ = δ(µ)`; `t ≥ √d > 1` (§4); `X_v = ϕ(σ(v))`.

**Formalization Note.** `E|V(o)|² < ∞` is `MemLp … 2`; the convergence is `‖V^{(L)}(o) − V(o)‖_{L²(ν̃)} → 0`. -/
theorem lemma_D_5 {r : ℕ} (p : SBMParams r) (t : ℝ) (ht : Real.sqrt p.d ≤ t) (μ : ℝ) (htμ : t < μ)
    (ϕ : Fin r → ℝ) (hϕ : (signal p).mulVec ϕ = μ • ϕ) (hϕn : ∑ a, p.pi a * ϕ a ^ 2 = 1) :
    MemLp (fun ω => Vtree p ϕ 1 t (deltaOf p.d t μ) [] ω) 2 (mgwLaw p) ∧
    Tendsto (fun L : ℕ => eLpNorm (fun ω =>
        vf (treeGraph ω.1) (label ω) ϕ 1 t (deltaOf p.d t μ) L [] -
          Vtree p ϕ 1 t (deltaOf p.d t μ) [] ω) 2 (mgwLaw p)) atTop (𝓝 0) := by sorry

end BetheKS
