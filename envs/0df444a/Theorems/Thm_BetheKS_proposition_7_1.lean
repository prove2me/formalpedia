-- Prove2me | Theorems.Thm_BetheKS_proposition_7_1
-- name    : BetheKS.proposition_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:33.77464+00:00
-- url     : https://prove2.me/theorems/2384a294-f85d-4adf-a127-333770de11f7
-- title:
--   Proposition 7.1 — local approximate eigenvectors $V_{i,n}$ on the finite SBM
-- statement:
--   Fix a sign $s\in\{\pm1\}$ and $t\ge\sqrt d$ below every $|\mu|$ for $\mu$ informative of sign $s$ (for $s=1$: $\sqrt d\le t<\mu^+_{r_+}$, §7). Relabel the informative eigenvalues of that sign and their real eigenfunctions, orthonormal in $L^2(\pi)$, as $\mu_1,\dots,\mu_{r_s}$, $\phi_1,\dots,\phi_{r_s}$; let $\delta_i=\delta(|\mu_i|)$ and let $V_i$ be the vertex field of Definition 6.1 on the labelled tree $(T,o)\sim\widetilde\nu$ (with $-\Gamma$, $-t$ when $s=-1$).
--   Let $s_i^2:=\mathbb E[V_i(o)^2]>0$ and $a_i:=\mathbb E[V_i(o)X_i(o)]$. There are deterministic sequences $L(n),M(n)\to\infty$ such that, for $V_{i,n}(u):=V_i^{(L(n),M(n))}(G_n,u)$:
--
--   1. $\frac1n\langle V_{i,n},V_{j,n}\rangle\to\mathbf 1\{i=j\}s_i^2$ and $\frac1n\langle V_{i,n},X_j\rangle\to\mathbf 1\{i=j\}a_i$ in $L^2$;
--   2. $\frac1n\|(H(st,G_n)+\delta_iI)V_{i,n}\|^2\to0$;
--   3. the empirical measure $\frac1n\sum_{u}\delta_{(\sigma(u),V_{1,n}(u),\dots,V_{r_s,n}(u))}$ converges weakly in probability to the law of $(\sigma(o),V_1(o),\dots,V_{r_s}(o))$.
--
--   These approximate eigenvectors have vanishing residual and nonvanishing planted correlation; Proposition 7.2 identifies them with outlier eigenvectors.
--
--   **Formalization Note** The positivity $s_i^2>0$ is asserted.
--
--   Differences from the source:
--
--   - generalization: Proposition 7.1 for H(t, G_n) and the positive informative eigenvalues → a sign s ∈ {±1}, with H(st, G_n), δ_i = δ(|μ_i|) and the sign-s fields; reason: the proof of Theorem 2.2 (p.12) asserts the negative case; s = 1 is the printed proposition
--   - reading: deterministic sequences L(n), M(n) → L(n), M(n) chosen before the label sequence σ_n; reason: deterministic = not depending on the sample; the law of G_n is the same for every exact-size labeling up to relabeling vertices
--   - encoding: (2): (1/n)‖(H + δ_i I)V_{i,n}‖² → 0 → convergence in L²; reason: App. E proves (1) and (2) 'in L²'
--   - encoding: weak convergence in probability of the empirical measure → for every bounded g on [r] × ℝ^{r_s}, continuous in the second argument, ∫ g dη_n → ∫ g dη in probability; reason: equivalent for a deterministic limit on this Polish space
--   - encoding: ϕ_1,…,ϕ_{r_s} the relabelled eigenfunctions → any real eigenfunctions of the μ_i orthonormal in L²(π); reason: the paper's choice is one of them
--   - encoding: n → ∞ with |σ⁻¹(i)| = π_i n → n → ∞ along 𝒩_π = {n : π_i n ∈ ℕ ∀ i}, for every sequence of exact-size label maps σ_n; reason: the paper's deterministic community-size convention (p.4); the statement is uniform over the labelings
--   - encoding: π a distribution on [r] → every π_a > 0; reason: the r eigenfunctions orthonormal in L²(π) that the paper uses exist only then; excludes undefined cases
--   - encoding: edge probability P_{σ(u)σ(v)}/n → min(1, P_{σ(u)σ(v)}/n); reason: affects only finitely many n, not the limits
--   - encoding: the multitype Galton–Watson tree ν̃ of Definition 5.1 → the Poi(d) tree with labels broadcast by the kernel Q_{ij}/d from a π-distributed root; reason: Poisson thinning with Σ_j Q_ij = d gives Poi(Q_ij) children of type j independently over j: the same law (children ordered)
--   - encoding: Ω the locally finite rooted trees, ν the Poi(d) Galton–Watson law → offspring functions on Ulam–Harris words (children ordered) with i.i.d. Poi(d) coordinates; reason: the tree read off has law ν and, given the root degree, the forward subtrees are i.i.d. ν, which is all the arguments use; κ, h, δ(μ) are unchanged
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Proposition 7.1, p.11 (PDF p.12); proof in App. E, pp.24–25

import Mathlib
import Definitions.Def_BetheKS_sbmProb
import Definitions.Def_BetheKS_treeVertexField
import Definitions.Def_BetheKS_transferOp

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace BetheKS

open Classical

/-- **Proposition 7.1** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), p.11
(PDF p.12). In §7 (p.11), fix `√d ≤ t < µ⁺_{r₊}` and relabel the positive informative eigenvalues and
eigenfunctions as `µ₁,…,µ_{r₊}`, `ϕ₁,…,ϕ_{r₊}`. Let `δᵢ = δ(µᵢ)`, `sᵢ² := E[Vᵢ(o)²] > 0` and
`aᵢ := E[Vᵢ(o) Xᵢ(o)]`. There are deterministic sequences `L(n), M(n) → ∞` such that, for
`Vᵢ,ₙ(u) := Vᵢ^{(L(n),M(n))}(Gₙ, u)`:
1. `(1/n)⟨Vᵢ,ₙ, Vⱼ,ₙ⟩ → 1{i=j} sᵢ²` and `(1/n)⟨Vᵢ,ₙ, Xⱼ⟩ → 1{i=j} aᵢ` in `L²`;
2. `(1/n)‖(H(t, Gₙ) + δᵢ I) Vᵢ,ₙ‖² → 0`;
3. the empirical measure `(1/n) ∑_{u} δ_{(σ(u), V₁,ₙ(u), …, V_{r₊},ₙ(u))}` converges weakly in
   probability to the law of `(σ(o), V₁(o), …, V_{r₊}(o))`.

**Formalization Note.** Stated for a sign `s ∈ {±1}`: `s = 1` is the printed proposition; `s = −1`
is the negative-eigenvalue version the proof of Theorem 2.2 (p.12) uses, with `H(−t, Gₙ)`, the
negative informative eigenvalues, `δᵢ = δ(|µᵢ|)`, and the sign-`s` fields (`−Γ`, `−t`). The `ϕᵢ` are
any real eigenfunctions orthonormal in `L²(π)`. `L(n), M(n)` are chosen before the labeling sequence.
The limit in (2) is in `L²`. Weak convergence in probability to the deterministic law is stated as:
for every bounded continuous `g` on `[r] × ℝ^{r₊}`, `∫ g dηₙ → ∫ g dη` in probability. -/
theorem proposition_7_1 {r : ℕ} (p : SBMParams r) (s : ℝ) (hs : s = 1 ∨ s = -1) (t : ℝ)
    (ht : Real.sqrt p.d ≤ t) (ht' : ∀ μ ∈ sgnInf p s, t < |μ|)
    (ϕ : Fin (sgnInf p s).length → Fin r → ℝ)
    (hϕ : ∀ i, (signal p).mulVec (ϕ i) = (sgnInf p s).get i • ϕ i)
    (hϕo : ∀ i j, ∑ a, p.pi a * ϕ i a * ϕ j a = if i = j then 1 else 0) :
    (∀ i, 0 < ∫ ω, (Vtree p (ϕ i) s t (deltaOf p.d t |(sgnInf p s).get i|) [] ω) ^ 2 ∂mgwLaw p) ∧
    ∃ Ls Ms : ℕ → ℕ, Tendsto Ls atTop atTop ∧ Tendsto Ms atTop atTop ∧
      ∀ σs : ∀ n : ℕ, Fin n → Fin r, IsExactSeq p σs →
        (∀ i j, ConvL2 p σs
          (fun n G => (1 / (n : ℝ)) * ∑ u,
            vfIter G (σs n) (ϕ i) s t (deltaOf p.d t |(sgnInf p s).get i|) (Ls n) (Ms n) u *
              vfIter G (σs n) (ϕ j) s t (deltaOf p.d t |(sgnInf p s).get j|) (Ls n) (Ms n) u)
          (if i = j then ∫ ω, (Vtree p (ϕ i) s t (deltaOf p.d t |(sgnInf p s).get i|) [] ω) ^ 2 ∂mgwLaw p
            else 0)) ∧
        (∀ i j, ConvL2 p σs
          (fun n G => (1 / (n : ℝ)) * ∑ u,
            vfIter G (σs n) (ϕ i) s t (deltaOf p.d t |(sgnInf p s).get i|) (Ls n) (Ms n) u *
              ϕ j (σs n u))
          (if i = j then ∫ ω, Vtree p (ϕ i) s t (deltaOf p.d t |(sgnInf p s).get i|) [] ω *
              ϕ i (label ω []) ∂mgwLaw p
            else 0)) ∧
        (∀ i, ConvL2 p σs
          (fun n G => (1 / (n : ℝ)) * ∑ u,
            (bhApply G (s * t)
                (vfIter G (σs n) (ϕ i) s t (deltaOf p.d t |(sgnInf p s).get i|) (Ls n) (Ms n)) u +
              deltaOf p.d t |(sgnInf p s).get i| *
                vfIter G (σs n) (ϕ i) s t (deltaOf p.d t |(sgnInf p s).get i|) (Ls n) (Ms n) u) ^ 2)
          0) ∧
        (∀ g : Fin r → (Fin (sgnInf p s).length → ℝ) → ℝ, (∀ a, Continuous (g a)) →
          (∃ C : ℝ, ∀ a x, |g a x| ≤ C) →
          ConvInProb p σs
            (fun n G => (1 / (n : ℝ)) * ∑ u, g (σs n u)
              (fun i => vfIter G (σs n) (ϕ i) s t (deltaOf p.d t |(sgnInf p s).get i|) (Ls n) (Ms n) u))
            (∫ ω, g (label ω [])
              (fun i => Vtree p (ϕ i) s t (deltaOf p.d t |(sgnInf p s).get i|) [] ω) ∂mgwLaw p)) := by sorry

end BetheKS
