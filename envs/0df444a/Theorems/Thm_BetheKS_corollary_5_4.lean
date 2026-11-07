-- Prove2me | Theorems.Thm_BetheKS_corollary_5_4
-- name    : BetheKS.corollary_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:47.753701+00:00
-- url     : https://prove2.me/theorems/1431ffb4-aeed-41d9-bca9-06276099ce23
-- title:
--   Corollary 5.4 — messages $b_{u\to v}$ on all directed edges of the multitype tree
-- statement:
--   Suppose $G$ is a rooted multitype Galton–Watson tree, in the setting of §5. There exist random variables $(b_{u\to v})_{(u,v)\in E}$ such that, for every $(u,v)$,
--   $$
--   b_{u\to v}=\Gamma^{(v)}_u\sum_{w\sim u,\ w\ne v}b_{w\to u}.
--   $$
--   Moreover, $b^{(L)}_{u\to v}\to b_{u\to v}$ in $L^2$ as $L\to\infty$.
--
--   **Formalization Note** The recursion holds almost surely, simultaneously for all directed edges; the convergence is for each pair of words $(u,v)$ on the event $u\sim v$.
--
--   Differences from the source:
--
--   - encoding: §5 preamble: μ_i > t an eigenvalue of Q with eigenvector ϕ_i, δ = δ(μ_i) → hypotheses t ≥ √d, t < μ, Qϕ = μϕ, Σ_a π_a ϕ(a)² = 1, and δ := deltaOf d t μ; reason: the section's standing assumptions; the normalization is the paper's L²(π) convention
--   - encoding: convergence in L² → eLpNorm of the difference in L²(ν̃) tends to 0; reason: the definition of L² convergence; the norm is ℝ≥0∞-valued, so no integrability side condition hides in it
--   - encoding: the multitype Galton–Watson tree ν̃ of Definition 5.1 → the Poi(d) tree with labels broadcast by the kernel Q_{ij}/d from a π-distributed root; reason: Poisson thinning with Σ_j Q_ij = d gives Poi(Q_ij) children of type j independently over j: the same law (children ordered)
--   - encoding: Ω the locally finite rooted trees, ν the Poi(d) Galton–Watson law → offspring functions on Ulam–Harris words (children ordered) with i.i.d. Poi(d) coordinates; reason: the tree read off has law ν and, given the root degree, the forward subtrees are i.i.d. ν, which is all the arguments use; κ, h, δ(μ) are unchanged
--   - encoding: π a distribution on [r] → every π_a > 0; reason: the r eigenfunctions orthonormal in L²(π) that the paper uses exist only then; excludes undefined cases
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Corollary 5.4, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_BetheKS_treeVertexField
import Definitions.Def_BetheKS_transferOp

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace BetheKS

open Classical

/-- **Corollary 5.4** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), p.9
(PDF p.10): suppose `G` is a rooted multitype Galton–Watson tree. There exist random variables
`(b_{u→v})_{(u,v) ∈ E}` such that, for every `(u, v)`, `b_{u→v} = Γ_u^{(v)} ∑_{w∼u, w≠v} b_{w→u}`.
Moreover, `b^{(L)}_{u→v} → b_{u→v}` in `L²` as `L → ∞`.

§5 preamble (p.8): `µ > t` is an eigenvalue of `Q` with eigenfunction `ϕ` (normalized in `L²(π)`), `ρ = µ/d`, `δ = δ(µ)`; `t ≥ √d > 1` (§4); `X_v = ϕ(σ(v))`.

**Formalization Note.** The `b_{u→v}` are random variables: each `B u v` is a.e. strongly
measurable for `ν̃`. The recursion holds `ν̃`-a.s. simultaneously for all directed edges; the
`L²` convergence is for every pair of words `(u, v)` on the event that `u ∼ v`. -/
theorem corollary_5_4 {r : ℕ} (p : SBMParams r) (t : ℝ) (ht : Real.sqrt p.d ≤ t) (μ : ℝ) (htμ : t < μ)
    (ϕ : Fin r → ℝ) (hϕ : (signal p).mulVec ϕ = μ • ϕ) (hϕn : ∑ a, p.pi a * ϕ a ^ 2 = 1) :
    ∃ B : List ℕ → List ℕ → LTData r → ℝ,
      (∀ u v : List ℕ, AEStronglyMeasurable (B u v) (mgwLaw p)) ∧
      (∀ᵐ ω ∂mgwLaw p, ∀ u v : List ℕ, (treeGraph ω.1).Adj u v →
        B u v ω = cav (treeGraph ω.1) t (deltaOf p.d t μ) u v *
          ∑ w ∈ ((treeGraph ω.1).neighborFinset u).erase v, B w u ω) ∧
      ∀ u v : List ℕ, Tendsto (fun L : ℕ => eLpNorm (fun ω =>
          if (treeGraph ω.1).Adj u v then
            msg (treeGraph ω.1) (label ω) ϕ 1 t (deltaOf p.d t μ) L u v - B u v ω else 0) 2
          (mgwLaw p)) atTop (𝓝 0) := by sorry

end BetheKS
