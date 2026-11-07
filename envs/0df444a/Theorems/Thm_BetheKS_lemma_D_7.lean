-- Prove2me | Theorems.Thm_BetheKS_lemma_D_7
-- name    : BetheKS.lemma_D_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:42.4732+00:00
-- url     : https://prove2.me/theorems/55dcce7a-4386-4d6f-832c-f0046031ebfb
-- title:
--   Lemma D.7 — $V^{(L,M)}(o)\to V^{(L)}(o)$ and residuals converge in $L^2$ as $M\to\infty$
-- statement:
--   On the Galton–Watson tree, in the setting of §5, for every $L\ge0$, as $M\to\infty$,
--   $$
--   V^{(L,M)}(o)\longrightarrow V^{(L)}(o)\qquad\text{and}\qquad\big[(H+\delta I)V^{(L,M)}\big](o)\longrightarrow\big[(H+\delta I)V^{(L)}\big](o),
--   $$
--   both in $L^2$.
--
--   Differences from the source:
--
--   - encoding: §5 preamble: μ_i > t an eigenvalue of Q with eigenvector ϕ_i, δ = δ(μ_i) → hypotheses t ≥ √d, t < μ, Qϕ = μϕ, Σ_a π_a ϕ(a)² = 1, and δ := deltaOf d t μ; reason: the section's standing assumptions; the normalization is the paper's L²(π) convention
--   - encoding: convergence in L² → eLpNorm of the difference in L²(ν̃) tends to 0; reason: the definition of L² convergence; the norm is ℝ≥0∞-valued, so no integrability side condition hides in it
--   - encoding: the multitype Galton–Watson tree ν̃ of Definition 5.1 → the Poi(d) tree with labels broadcast by the kernel Q_{ij}/d from a π-distributed root; reason: Poisson thinning with Σ_j Q_ij = d gives Poi(Q_ij) children of type j independently over j: the same law (children ordered)
--   - encoding: Ω the locally finite rooted trees, ν the Poi(d) Galton–Watson law → offspring functions on Ulam–Harris words (children ordered) with i.i.d. Poi(d) coordinates; reason: the tree read off has law ν and, given the root degree, the forward subtrees are i.i.d. ν, which is all the arguments use; κ, h, δ(μ) are unchanged
--   - encoding: π a distribution on [r] → every π_a > 0; reason: the r eigenfunctions orthonormal in L²(π) that the paper uses exist only then; excludes undefined cases
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Lemma D.7, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_BetheKS_treeVertexField
import Definitions.Def_BetheKS_transferOp

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace BetheKS

open Classical

/-- **Lemma D.7** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), p.23
(PDF p.24): on the Galton–Watson tree, for every `L ≥ 0`, as `M → ∞`,
`V^{(L,M)}(o) → V^{(L)}(o)` and `[(H + δI)V^{(L,M)}](o) → [(H + δI)V^{(L)}](o)`, both in `L²`.

§5 preamble (p.8): `µ > t` is an eigenvalue of `Q` with eigenfunction `ϕ` (normalized in `L²(π)`), `ρ = µ/d`, `δ = δ(µ)`; `t ≥ √d > 1` (§4); `X_v = ϕ(σ(v))`. -/
theorem lemma_D_7 {r : ℕ} (p : SBMParams r) (t : ℝ) (ht : Real.sqrt p.d ≤ t) (μ : ℝ) (htμ : t < μ)
    (ϕ : Fin r → ℝ) (hϕ : (signal p).mulVec ϕ = μ • ϕ) (hϕn : ∑ a, p.pi a * ϕ a ^ 2 = 1) :
    ∀ L : ℕ,
      Tendsto (fun M : ℕ => eLpNorm (fun ω =>
          vfIter (treeGraph ω.1) (label ω) ϕ 1 t (deltaOf p.d t μ) L M [] -
            vf (treeGraph ω.1) (label ω) ϕ 1 t (deltaOf p.d t μ) L []) 2 (mgwLaw p)) atTop (𝓝 0) ∧
      Tendsto (fun M : ℕ => eLpNorm (fun ω =>
          (bhApply (treeGraph ω.1) t (vfIter (treeGraph ω.1) (label ω) ϕ 1 t (deltaOf p.d t μ) L M) [] +
            deltaOf p.d t μ * vfIter (treeGraph ω.1) (label ω) ϕ 1 t (deltaOf p.d t μ) L M []) -
          (bhApply (treeGraph ω.1) t (vf (treeGraph ω.1) (label ω) ϕ 1 t (deltaOf p.d t μ) L) [] +
            deltaOf p.d t μ * vf (treeGraph ω.1) (label ω) ϕ 1 t (deltaOf p.d t μ) L [])) 2 (mgwLaw p))
        atTop (𝓝 0) := by sorry

end BetheKS
