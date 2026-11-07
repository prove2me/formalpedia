-- Prove2me | Theorems.Thm_BetheKS_lemma_E_1
-- name    : BetheKS.lemma_E_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:32.270551+00:00
-- url     : https://prove2.me/theorems/15ad9faa-4959-4d62-8adf-05a133e17a9f
-- title:
--   Lemma E.1 (Local averaging; standard, [9, Props 35–36]) — $\frac1n\sum_uf(G_n,u)\to\mathbb Ef(T,o)$ in $L^2$
-- statement:
--   Fix $R\ge0$. Let $f$ be a real function on rooted graphs $(G,u)$ with vertex labels in $[r]$. Suppose $f$ only depends on $B_R(G,u)$ and that for some fixed $C,p<\infty$
--   $$
--   |f(G,u)|\le C|B_R(G,u)|^p\qquad\text{for all }(G,u).
--   $$
--   Then, for $G_n\sim\mathrm{SBM}_n(P,\pi)$ and its limiting labelled Galton–Watson tree $(T,o)\sim\widetilde\nu$,
--   $$
--   \frac1n\sum_{u\in V(G_n)}f(G_n,u)\longrightarrow\mathbb Ef(T,o)\qquad\text{in }L^2 .
--   $$
--   The paper cites this as standard ([9, Propositions 35–36], Bordenave–Lelarge–Massoulié); it transfers tree moments of local fields to the finite graph.
--
--   **Formalization Note** $f$ is a function of rooted labelled locally finite graphs; "only depends on $B_R(G,u)$" means $f$ agrees on rooted labelled graphs whose $R$-balls are isomorphic. The exponent $p$ is real.
--
--   Differences from the source:
--
--   - encoding: n → ∞ with |σ⁻¹(i)| = π_i n → n → ∞ along 𝒩_π = {n : π_i n ∈ ℕ ∀ i}, for every sequence of exact-size label maps σ_n; reason: the paper's deterministic community-size convention (p.4); the statement is uniform over the labelings
--   - encoding: π a distribution on [r] → every π_a > 0; reason: the r eigenfunctions orthonormal in L²(π) that the paper uses exist only then; excludes undefined cases
--   - encoding: edge probability P_{σ(u)σ(v)}/n → min(1, P_{σ(u)σ(v)}/n); reason: affects only finitely many n, not the limits
--   - encoding: the multitype Galton–Watson tree ν̃ of Definition 5.1 → the Poi(d) tree with labels broadcast by the kernel Q_{ij}/d from a π-distributed root; reason: Poisson thinning with Σ_j Q_ij = d gives Poi(Q_ij) children of type j independently over j: the same law (children ordered)
--   - encoding: Ω the locally finite rooted trees, ν the Poi(d) Galton–Watson law → offspring functions on Ulam–Harris words (children ordered) with i.i.d. Poi(d) coordinates; reason: the tree read off has law ν and, given the root degree, the forward subtrees are i.i.d. ν, which is all the arguments use; κ, h, δ(μ) are unchanged
--   - encoding: f a real function on rooted graphs with labels in [r] that only depends on B_R(G,u), with |f| ≤ C|B_R(G,u)|^p → f on bundled rooted vertex-labelled locally finite graphs (RLGraph), equal on any two whose induced balls of radius R are isomorphic by a root- and label-preserving graph isomorphism; the exponent p is real; reason: what "only depends on B_R(G,u)" means; the degrees of the paper's graphs are finite
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Lemma E.1, p.24 (PDF p.25)

import Mathlib
import Definitions.Def_BetheKS_sbmProb
import Definitions.Def_BetheKS_treeVertexField

set_option autoImplicit false

open MeasureTheory

namespace BetheKS

/-- **Lemma E.1 (Local averaging)** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256
4da41e16…), p.24 (PDF p.25), cited there as standard ([9, Propositions 35–36]): fix `R ≥ 0`. Let `f`
be a real function on rooted graphs `(G, u)` with vertex labels in `[r]`. Suppose `f` only depends on
`B_R(G, u)` and that for some fixed `C, p < ∞`, `|f(G, u)| ≤ C |B_R(G, u)|^p` for all `(G, u)`. Then
`(1/n) ∑_{u ∈ V(Gₙ)} f(Gₙ, u) → E f(T, o)` in `L²`.

Here `Gₙ ∼ SBMₙ(P, π)` with labels `σ` and `(T, o) ∼ ν̃` is its limiting multitype Galton–Watson tree
(§7, p.11).

**Formalization Note.** `f` is defined on rooted labelled locally finite graphs (`RLGraph`); "only
depends on `B_R(G,u)`" means `f` agrees on graphs with isomorphic rooted labelled `R`-balls. The
exponent `p` is real. The convergence is `E|(1/n)∑ᵤ f(Gₙ, u) − E f(T, o)|² → 0` along `𝒩_π`, for every
exact-size labeling sequence. -/
theorem lemma_E_1 {r : ℕ} (p : SBMParams r) (R : ℕ) (f : RLGraph r → ℝ)
    (hf : ∀ X Y : RLGraph r, BallIso X Y R → f X = f Y)
    (C q : ℝ) (hbound : ∀ X : RLGraph r, |f X| ≤ C * (ballCard X R : ℝ) ^ q)
    (σs : ∀ n : ℕ, Fin n → Fin r) (hσ : IsExactSeq p σs) :
    ConvL2 p σs (fun n G => (1 / (n : ℝ)) * ∑ u, f (finRL G (σs n) u))
      (∫ ω, f (treeRL ω) ∂mgwLaw p) := by sorry

end BetheKS
