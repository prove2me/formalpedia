-- Prove2me | Theorems.Thm_BetheKS_proposition_6_2
-- name    : BetheKS.proposition_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:39.265199+00:00
-- url     : https://prove2.me/theorems/6023191d-b0a5-4b62-ac87-f849f469788d
-- title:
--   Proposition 6.2 — $V$ is an eigenvector of $H(t,T)$: $(H(t,T)V)(u)=-\delta V(u)$
-- statement:
--   On the Galton–Watson tree $T\sim\widetilde\nu$, in the setting of §5, the vertex field $V$ of Definition 6.1 satisfies
--   $$
--   (H(t,T)V)(u)=-\delta V(u)
--   $$
--   for every vertex $u$, where $(H(t,T)V)(u)=(t^2-1+\deg u)V(u)-t\sum_{w\sim u}V(w)$. The planted direction thus produces an eigenvector with eigenvalue $-\delta(\mu)$ on the limiting tree.
--
--   **Formalization Note** Almost surely, simultaneously at every vertex.
--
--   Differences from the source:
--
--   - encoding: §5 preamble: μ_i > t an eigenvalue of Q with eigenvector ϕ_i, δ = δ(μ_i) → hypotheses t ≥ √d, t < μ, Qϕ = μϕ, Σ_a π_a ϕ(a)² = 1, and δ := deltaOf d t μ; reason: the section's standing assumptions; the normalization is the paper's L²(π) convention
--   - encoding: the multitype Galton–Watson tree ν̃ of Definition 5.1 → the Poi(d) tree with labels broadcast by the kernel Q_{ij}/d from a π-distributed root; reason: Poisson thinning with Σ_j Q_ij = d gives Poi(Q_ij) children of type j independently over j: the same law (children ordered)
--   - encoding: Ω the locally finite rooted trees, ν the Poi(d) Galton–Watson law → offspring functions on Ulam–Harris words (children ordered) with i.i.d. Poi(d) coordinates; reason: the tree read off has law ν and, given the root degree, the forward subtrees are i.i.d. ν, which is all the arguments use; κ, h, δ(μ) are unchanged
--   - encoding: π a distribution on [r] → every π_a > 0; reason: the r eigenfunctions orthonormal in L²(π) that the paper uses exist only then; excludes undefined cases
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Proposition 6.2, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_BetheKS_treeVertexField
import Definitions.Def_BetheKS_transferOp

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace BetheKS

open Classical

/-- **Proposition 6.2** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), p.10
(PDF p.11): on the Galton–Watson tree, the vertex field `V` of Definition 6.1 satisfies
`(H(t, T) V)(u) = −δ V(u)`.

§5 preamble (p.8): `µ > t` is an eigenvalue of `Q` with eigenfunction `ϕ` (normalized in `L²(π)`), `ρ = µ/d`, `δ = δ(µ)`; `t ≥ √d > 1` (§4); `X_v = ϕ(σ(v))`.

**Formalization Note.** `ν̃`-a.s., at every vertex `u`; `(H(t,T)V)(u) = (t² − 1 + deg u) V(u) − t ∑_{w∼u} V(w)`. -/
theorem proposition_6_2 {r : ℕ} (p : SBMParams r) (t : ℝ) (ht : Real.sqrt p.d ≤ t) (μ : ℝ) (htμ : t < μ)
    (ϕ : Fin r → ℝ) (hϕ : (signal p).mulVec ϕ = μ • ϕ) (hϕn : ∑ a, p.pi a * ϕ a ^ 2 = 1) :
    ∀ᵐ ω ∂mgwLaw p, ∀ u : List ℕ, IsVertex ω.1 u →
      bhApply (treeGraph ω.1) t (fun v => Vtree p ϕ 1 t (deltaOf p.d t μ) v ω) u =
        -(deltaOf p.d t μ) * Vtree p ϕ 1 t (deltaOf p.d t μ) u ω := by sorry

end BetheKS
