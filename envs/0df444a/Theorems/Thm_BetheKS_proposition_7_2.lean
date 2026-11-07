-- Prove2me | Theorems.Thm_BetheKS_proposition_7_2
-- name    : BetheKS.proposition_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:13.129098+00:00
-- url     : https://prove2.me/theorems/67534f18-c213-4c6e-9771-c5f379540ede
-- title:
--   Proposition 7.2 — orthonormal outlier eigenvectors of $H(t,G_n)$ approximate $V_{i,n}/\|V_{i,n}\|_2$
-- statement:
--   Fix a sign $s\in\{\pm1\}$ and $t\ge\sqrt d$ below every $|\mu|$ for $\mu$ informative of sign $s$ (for $s=1$: $\sqrt d\le t<\mu^+_{r_+}$, §7). Relabel the informative eigenvalues of that sign and their real eigenfunctions, orthonormal in $L^2(\pi)$, as $\mu_1,\dots,\mu_{r_s}$, $\phi_1,\dots,\phi_{r_s}$; let $\delta_i=\delta(|\mu_i|)$ and let $V_i$ be the vertex field of Definition 6.1 on the labelled tree $(T,o)\sim\widetilde\nu$ (with $-\Gamma$, $-t$ when $s=-1$).
--   Let $V_{i,n}=V_i^{(L(n),M(n))}(G_n,\cdot)$ be the finite-graph fields of Proposition 7.1, for sequences $L(n),M(n)\to\infty$ satisfying its conclusions (1) and (2). Then there exist orthonormal eigenvectors $v_{1,n},\dots,v_{r_s,n}$ of $H(st,G_n)$, with eigenvalues $-\delta_{1,n},\dots,-\delta_{r_s,n}$, such that
--   $$
--   \delta_{i,n}\xrightarrow{\mathbb P}\delta_i\qquad(1\le i\le r_s).
--   $$
--   For each distinct $\mu\in\{\mu_1,\dots,\mu_{r_s}\}$, with $J_\mu=\{i:\mu_i=\mu\}$, there is an orthogonal matrix $O_{\mu,n}$ indexed by $J_\mu$ such that
--   $$
--   \max_{i\in J_\mu}\Big\|\sum_{j\in J_\mu}(O_{\mu,n})_{ji}v_{j,n}-\frac{V_{i,n}}{\|V_{i,n}\|_2}\Big\|_2\xrightarrow{\mathbb P}0 .
--   $$
--   In particular, if $\mu_i$ is simple, the sign of $v_{i,n}$ can be chosen so that $\|v_{i,n}-V_{i,n}/\|V_{i,n}\|_2\|_2\xrightarrow{\mathbb P}0$.
--
--   This identifies the approximate eigenvectors of Proposition 7.1 with actual spectral subspaces of the Bethe Hessian.
--
--   **Formalization Note** Eigenvectors, eigenvalues, orthogonal matrices and signs are functions of the graph; the eigen-equations are required for all large $n$.
--
--   Differences from the source:
--
--   - generalization: Proposition 7.2 for H(t, G_n) and the positive informative eigenvalues → a sign s ∈ {±1}: H(st, G_n), the informative eigenvalues of sign s, δ_i = δ(|μ_i|), sign-s fields; reason: the proof of Theorem 2.2 (p.12) asserts the negative case ('the same convergence estimates apply'); s = 1 is the printed proposition
--   - reading: V_{i,n} the fields of Proposition 7.1 → for any L(n), M(n) → ∞ for which conclusions (1), (2) of Proposition 7.1 hold; reason: the proof of Proposition 7.2 uses only these conclusions; it includes the sequences of Proposition 7.1
--   - encoding: max over i ∈ J_μ tends to 0 in probability → for each i ∈ J_μ, the norm tends to 0 in probability; reason: J_μ is finite
--   - encoding: n → ∞ with |σ⁻¹(i)| = π_i n → n → ∞ along 𝒩_π = {n : π_i n ∈ ℕ ∀ i}, for every sequence of exact-size label maps σ_n; reason: the paper's deterministic community-size convention (p.4); the statement is uniform over the labelings
--   - encoding: π a distribution on [r] → every π_a > 0; reason: the r eigenfunctions orthonormal in L²(π) that the paper uses exist only then; excludes undefined cases
--   - encoding: edge probability P_{σ(u)σ(v)}/n → min(1, P_{σ(u)σ(v)}/n); reason: affects only finitely many n, not the limits
--   - encoding: the multitype Galton–Watson tree ν̃ of Definition 5.1 → the Poi(d) tree with labels broadcast by the kernel Q_{ij}/d from a π-distributed root; reason: Poisson thinning with Σ_j Q_ij = d gives Poi(Q_ij) children of type j independently over j: the same law (children ordered)
--   - encoding: Ω the locally finite rooted trees, ν the Poi(d) Galton–Watson law → offspring functions on Ulam–Harris words (children ordered) with i.i.d. Poi(d) coordinates; reason: the tree read off has law ν and, given the root degree, the forward subtrees are i.i.d. ν, which is all the arguments use; κ, h, δ(μ) are unchanged
--   - encoding: orthonormal eigenvectors v_{1,n},…,v_{r₊,n} of H(t, G_n) → v, the eigenvalues, O and the signs are functions of (n, G); orthonormality and the eigen-equations are required for every graph G and all large n; reason: r_s orthonormal vectors exist in ℝⁿ only for n ≥ r_s; the limits in probability are unaffected
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Proposition 7.2, p.11 (PDF p.12); proof in App. E, pp.25–26

import Mathlib
import Definitions.Def_BetheKS_sbmProb
import Definitions.Def_BetheKS_betheHessian
import Definitions.Def_BetheKS_treeVertexField
import Definitions.Def_BetheKS_transferOp

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace BetheKS

open Classical

/-- **Proposition 7.2** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), p.11
(PDF p.12): there exist orthonormal eigenvectors `v₁,ₙ,…,v_{r₊},ₙ` of `H(t, Gₙ)`, with eigenvalues
`−δ₁,ₙ,…,−δ_{r₊},ₙ`, such that `δᵢ,ₙ →ᴾ δᵢ` (`1 ≤ i ≤ r₊`). For each distinct `µ ∈ {µ₁,…,µ_{r₊}}`, with
`J_µ = {i : µᵢ = µ}`, there is an orthogonal matrix `O_{µ,n}` indexed by `J_µ` with
`max_{i∈J_µ} ‖∑_{j∈J_µ} (O_{µ,n})_{ji} vⱼ,ₙ − Vᵢ,ₙ/‖Vᵢ,ₙ‖₂‖₂ →ᴾ 0`. In particular, if `µᵢ` is simple, the
sign of `vᵢ,ₙ` can be chosen so that `‖vᵢ,ₙ − Vᵢ,ₙ/‖Vᵢ,ₙ‖₂‖₂ →ᴾ 0`.

Setting of §7 (p.11) as in Proposition 7.1; `Vᵢ,ₙ = Vᵢ^{(L(n),M(n))}(Gₙ, ·)` are the fields of
Proposition 7.1.

**Formalization Note.** Sign `s ∈ {±1}` as in Proposition 7.1 (`H(st, Gₙ)`). The proposition is
stated for any sequences `L(n), M(n) → ∞` for which conclusions (1) and (2) of Proposition 7.1 hold,
which is how its proof uses Proposition 7.1. The eigenvectors, eigenvalues, orthogonal matrices and
signs are functions of the graph; the eigen-equations are required for all large `n`. "max over
`J_µ` → 0 in probability" is stated for each `i ∈ J_µ` (finitely many). -/
theorem proposition_7_2 {r : ℕ} (p : SBMParams r) (s : ℝ) (hs : s = 1 ∨ s = -1) (t : ℝ)
    (ht : Real.sqrt p.d ≤ t) (ht' : ∀ μ ∈ sgnInf p s, t < |μ|)
    (ϕ : Fin (sgnInf p s).length → Fin r → ℝ)
    (hϕ : ∀ i, (signal p).mulVec (ϕ i) = (sgnInf p s).get i • ϕ i)
    (hϕo : ∀ i j, ∑ a, p.pi a * ϕ i a * ϕ j a = if i = j then 1 else 0)
    (σs : ∀ n : ℕ, Fin n → Fin r) (hσ : IsExactSeq p σs)
    (Ls Ms : ℕ → ℕ) (hL : Tendsto Ls atTop atTop) (hM : Tendsto Ms atTop atTop)
    (h1 : ∀ i j, ConvL2 p σs
      (fun n G => (1 / (n : ℝ)) * ∑ u,
        vfIter G (σs n) (ϕ i) s t (deltaOf p.d t |(sgnInf p s).get i|) (Ls n) (Ms n) u *
          vfIter G (σs n) (ϕ j) s t (deltaOf p.d t |(sgnInf p s).get j|) (Ls n) (Ms n) u)
      (if i = j then ∫ ω, (Vtree p (ϕ i) s t (deltaOf p.d t |(sgnInf p s).get i|) [] ω) ^ 2 ∂mgwLaw p
        else 0))
    (h1' : ∀ i j, ConvL2 p σs
      (fun n G => (1 / (n : ℝ)) * ∑ u,
        vfIter G (σs n) (ϕ i) s t (deltaOf p.d t |(sgnInf p s).get i|) (Ls n) (Ms n) u * ϕ j (σs n u))
      (if i = j then ∫ ω, Vtree p (ϕ i) s t (deltaOf p.d t |(sgnInf p s).get i|) [] ω *
          ϕ i (label ω []) ∂mgwLaw p
        else 0))
    (h2 : ∀ i, ConvL2 p σs
      (fun n G => (1 / (n : ℝ)) * ∑ u,
        (bhApply G (s * t)
            (vfIter G (σs n) (ϕ i) s t (deltaOf p.d t |(sgnInf p s).get i|) (Ls n) (Ms n)) u +
          deltaOf p.d t |(sgnInf p s).get i| *
            vfIter G (σs n) (ϕ i) s t (deltaOf p.d t |(sgnInf p s).get i|) (Ls n) (Ms n) u) ^ 2)
      0) :
    ∃ v : ∀ n : ℕ, SimpleGraph (Fin n) → Fin (sgnInf p s).length → EuclideanSpace ℝ (Fin n),
    ∃ lam : ∀ n : ℕ, SimpleGraph (Fin n) → Fin (sgnInf p s).length → ℝ,
      (∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n), Orthonormal ℝ (v n G) ∧
        ∀ i, Matrix.toEuclideanLin (bh (s * t) G) (v n G i) = (-lam n G i) • v n G i) ∧
      (∀ i, ConvInProb p σs (fun n G => lam n G i) (deltaOf p.d t |(sgnInf p s).get i|)) ∧
      (∀ μ ∈ sgnInf p s, ∃ O : ∀ n : ℕ, SimpleGraph (Fin n) →
          Matrix {i // (sgnInf p s).get i = μ} {i // (sgnInf p s).get i = μ} ℝ,
        (∀ (n : ℕ) (G : SimpleGraph (Fin n)), (O n G).transpose * O n G = 1) ∧
        ∀ i : {i // (sgnInf p s).get i = μ}, ConvInProb p σs
          (fun n G => ‖(∑ j : {i // (sgnInf p s).get i = μ}, O n G j i • v n G j.val) -
            (1 / ‖(WithLp.toLp 2 (fun u => vfIter G (σs n) (ϕ i.val) s t
                (deltaOf p.d t |(sgnInf p s).get i.val|) (Ls n) (Ms n) u) : EuclideanSpace ℝ (Fin n))‖) •
              (WithLp.toLp 2 (fun u => vfIter G (σs n) (ϕ i.val) s t
                (deltaOf p.d t |(sgnInf p s).get i.val|) (Ls n) (Ms n) u) : EuclideanSpace ℝ (Fin n))‖)
          0) ∧
      (∀ i, (sgnInf p s).count ((sgnInf p s).get i) = 1 →
        ∃ sg : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ, (∀ n G, sg n G = 1 ∨ sg n G = -1) ∧
          ConvInProb p σs
            (fun n G => ‖sg n G • v n G i -
              (1 / ‖(WithLp.toLp 2 (fun u => vfIter G (σs n) (ϕ i) s t
                  (deltaOf p.d t |(sgnInf p s).get i|) (Ls n) (Ms n) u) : EuclideanSpace ℝ (Fin n))‖) •
                (WithLp.toLp 2 (fun u => vfIter G (σs n) (ϕ i) s t
                  (deltaOf p.d t |(sgnInf p s).get i|) (Ls n) (Ms n) u) : EuclideanSpace ℝ (Fin n))‖)
            0) := by sorry

end BetheKS
