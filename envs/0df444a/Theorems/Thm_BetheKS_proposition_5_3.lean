-- Prove2me | Theorems.Thm_BetheKS_proposition_5_3
-- name    : BetheKS.proposition_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:43.597206+00:00
-- url     : https://prove2.me/theorems/f8074a9d-5772-4a16-a9d6-d74b7bc794f0
-- title:
--   Proposition 5.3 — the $L^2$ limit $b_u=\lim_Lb^{(L)}_u$ and $b_u=\Gamma_u\sum_{w\in\mathrm{ch}(u)}b_w$
-- statement:
--   Suppose $G\sim\widetilde\nu$ is the multitype Galton–Watson tree, in the setting of §5. There is an $L^2$ function $b_u:\widetilde\Omega\to\mathbb R$ such that
--   $$
--   \lim_{L\to\infty}b^{(L)}_u=b_u,\qquad b_u=\Gamma_u\sum_{w\in\operatorname{ch}(u)}b_w.\qquad(5.2)
--   $$
--   Here $b^{(L)}_u=b^{(L)}_{u\to p(u)}$ and $\Gamma_u=\Gamma_u^{(p(u))}$.
--
--   **Formalization Note** $u$ ranges over non-root vertices; the limit is in $L^2(\widetilde\nu)$ (App. C); the recursion holds almost surely at every non-root vertex.
--
--   Differences from the source:
--
--   - encoding: §5 preamble: μ_i > t an eigenvalue of Q with eigenvector ϕ_i, δ = δ(μ_i) → hypotheses t ≥ √d, t < μ, Qϕ = μϕ, Σ_a π_a ϕ(a)² = 1, and δ := deltaOf d t μ; reason: the section's standing assumptions; the normalization is the paper's L²(π) convention
--   - encoding: convergence in L² → eLpNorm of the difference in L²(ν̃) tends to 0; reason: the definition of L² convergence; the norm is ℝ≥0∞-valued, so no integrability side condition hides in it
--   - encoding: the multitype Galton–Watson tree ν̃ of Definition 5.1 → the Poi(d) tree with labels broadcast by the kernel Q_{ij}/d from a π-distributed root; reason: Poisson thinning with Σ_j Q_ij = d gives Poi(Q_ij) children of type j independently over j: the same law (children ordered)
--   - encoding: Ω the locally finite rooted trees, ν the Poi(d) Galton–Watson law → offspring functions on Ulam–Harris words (children ordered) with i.i.d. Poi(d) coordinates; reason: the tree read off has law ν and, given the root degree, the forward subtrees are i.i.d. ν, which is all the arguments use; κ, h, δ(μ) are unchanged
--   - encoding: π a distribution on [r] → every π_a > 0; reason: the r eigenfunctions orthonormal in L²(π) that the paper uses exist only then; excludes undefined cases
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Proposition 5.3, p.9 (PDF p.10), (5.2); proof in App. C, pp.18–19

import Mathlib
import Definitions.Def_BetheKS_treeVertexField
import Definitions.Def_BetheKS_transferOp

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace BetheKS

open Classical

/-- **Proposition 5.3** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), p.9
(PDF p.10): suppose `G ∼ ν̃` is the multitype Galton–Watson tree. There is an `L²` function
`b_u : Ω̃ → ℝ` such that `lim_{L→∞} b^{(L)}_u = b_u` and `b_u = Γ_u ∑_{w ∈ ch(u)} b_w` (5.2).

§5 preamble (p.8): `µ > t` is an eigenvalue of `Q` with eigenfunction `ϕ` (normalized in `L²(π)`), `ρ = µ/d`, `δ = δ(µ)`; `t ≥ √d > 1` (§4); `X_v = ϕ(σ(v))`.

**Formalization Note.** `u` ranges over non-root words (`b_u = b_{u→p(u)}`, Definition 5.2); the limit
is in `L²(ν̃)` (App. C: "`b^{(L)} → b` in `L²`"); (5.2) holds `ν̃`-a.s. at every vertex `u ≠ o`, with
`Γ_u = Γ_u^{(p(u))}` and `ch(u) = {j :: u : j < K(u)}`. -/
theorem proposition_5_3 {r : ℕ} (p : SBMParams r) (t : ℝ) (ht : Real.sqrt p.d ≤ t) (μ : ℝ) (htμ : t < μ)
    (ϕ : Fin r → ℝ) (hϕ : (signal p).mulVec ϕ = μ • ϕ) (hϕn : ∑ a, p.pi a * ϕ a ^ 2 = 1) :
    ∃ b : List ℕ → LTData r → ℝ,
      (∀ u : List ℕ, u ≠ [] → MemLp (b u) 2 (mgwLaw p) ∧
        Tendsto (fun L : ℕ => eLpNorm (fun ω => treeMsgUp ϕ 1 t (deltaOf p.d t μ) L u ω - b u ω) 2
          (mgwLaw p)) atTop (𝓝 0)) ∧
      ∀ᵐ ω ∂mgwLaw p, ∀ u : List ℕ, u ≠ [] → IsVertex ω.1 u →
        b u ω = cav (treeGraph ω.1) t (deltaOf p.d t μ) u u.tail *
          ∑ j ∈ Finset.range (ω.1 u), b (j :: u) ω := by sorry

end BetheKS
