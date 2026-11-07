-- Prove2me | Theorems.Thm_BetheKS_lemma_D_6
-- name    : BetheKS.lemma_D_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:27.299468+00:00
-- url     : https://prove2.me/theorems/9ec320d5-6b9a-46d2-b3d6-a3b94adbf48d
-- title:
--   Lemma D.6 — the residual $\mathbb E|[(H(t,T)+\delta I)V^{(L)}](o)|^2\to0$
-- statement:
--   On the labelled Galton–Watson tree, in the setting of §5, $\mathbb E|[(H(t,T)+\delta I)V^{(L)}](o)|^2\to0$ as $L\to\infty$, that is,
--   $$
--   \mathbb E\Big|(t^2-1+\delta+\deg(o))V^{(L)}(o)-t\sum_{w\sim o}V^{(L)}(w)\Big|^2\longrightarrow0\qquad(L\to\infty).\qquad(D.1)
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
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Lemma D.6, p.22 (PDF p.23), (D.1)

import Mathlib
import Definitions.Def_BetheKS_treeVertexField
import Definitions.Def_BetheKS_transferOp

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace BetheKS

open Classical

/-- **Lemma D.6** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), p.22
(PDF p.23): `E|[(H(t,T) + δI) V^{(L)}](o)|² → 0` as `L → ∞`, that is,
`E|(t² − 1 + δ + deg(o)) V^{(L)}(o) − t ∑_{w∼o} V^{(L)}(w)|² → 0` (D.1).

§5 preamble (p.8): `µ > t` is an eigenvalue of `Q` with eigenfunction `ϕ` (normalized in `L²(π)`), `ρ = µ/d`, `δ = δ(µ)`; `t ≥ √d > 1` (§4); `X_v = ϕ(σ(v))`. -/
theorem lemma_D_6 {r : ℕ} (p : SBMParams r) (t : ℝ) (ht : Real.sqrt p.d ≤ t) (μ : ℝ) (htμ : t < μ)
    (ϕ : Fin r → ℝ) (hϕ : (signal p).mulVec ϕ = μ • ϕ) (hϕn : ∑ a, p.pi a * ϕ a ^ 2 = 1) :
    Tendsto (fun L : ℕ => eLpNorm (fun ω =>
        bhApply (treeGraph ω.1) t (vf (treeGraph ω.1) (label ω) ϕ 1 t (deltaOf p.d t μ) L) [] +
          deltaOf p.d t μ * vf (treeGraph ω.1) (label ω) ϕ 1 t (deltaOf p.d t μ) L []) 2 (mgwLaw p))
      atTop (𝓝 0) := by sorry

end BetheKS
