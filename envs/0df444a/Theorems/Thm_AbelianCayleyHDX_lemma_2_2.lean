-- Prove2me | Theorems.Thm_AbelianCayleyHDX_lemma_2_2
-- name    : AbelianCayleyHDX.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:36:04.593201+00:00
-- url     : https://prove2.me/theorems/5c8084aa-04bd-44fd-bdd2-349f311d499e
-- title:
--   Lemma 2.2 — the link at $0$ controls every vertex link of $X_H$
-- statement:
--   Let $H$, $\rho$, $\varphi$ be as in Section 2.4 (distinct weight-three rows, constant positive column weight $\rho$, row space of minimum distance at least three, $\Gamma_H \cong \mathbb F_2^n$ via $\varphi$). If the vertex link of $0$ in $X_H$ is connected and
--   $$\big\|P_H|_{\mathbf 1^\perp}\big\| \le \lambda,$$
--   then $X_H$ has two-sided codimension-two local spectral norm at most $\lambda$: every vertex link is connected and a two-sided $\lambda$-spectral expander.
--
--   Differences from the source:
--   - encoding: $\Gamma_H = \mathbb F_2^M/R_H$ identified with $\mathbb F_2^n$ by $v + R_H \mapsto Bv$ → any $\mathbb F_2$-linear surjection $\varphi : \mathbb F_2^M \to \mathbb F_2^n$ with kernel $R_H$, $s_i = \varphi(e_i)$; reason: every such identification is of this form; the paper's $B$ gives one
--   - encoding: rows $[R]$ and columns $[M]$ → arbitrary finite index types, $M$ = number of columns; reason: a finite type is in bijection with $[M]$; no instance changes
--   - encoding: $\|P_H|_{\mathbf 1^\perp}\| \le \lambda$ → $\|P_H f\|_2 \le \lambda\|f\|_2$ for every $f$ with $\sum_i f_i = 0$ (Euclidean norm); reason: the link at $0$ is regular, so $\pi$ is uniform (p.8: "for regular graphs we omit the subscript $\pi$")
--   - encoding: the vertex link of $0$ is connected → the graph on the link vertices with positive-weight edges is connected (reflexive-transitive closure); reason: definition of connectivity for a weighted graph
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 2.2, p.10

import Mathlib
import Definitions.Def_AbelianCayleyHDX_IsGoodRelationMatrix
import Definitions.Def_AbelianCayleyHDX_PH
import Definitions.Def_AbelianCayleyHDX_relationComplex
import Definitions.Def_AbelianCayleyHDX_HasLocalSpectralNorm
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX

/-- **Lemma 2.2** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 2.2, p.10). For `X_H` as in Section 2.4 (relation matrix `H` with
distinct weight-three rows, constant positive column weight `ρ`, row space of minimum distance at
least three, `Γ_H ≅ 𝔽₂ⁿ` via `φ`): if the vertex link of `0` in `X_H` is connected and
`‖P_H|_{1^⊥}‖ ≤ λ`, then `X_H` has two-sided codimension-two local spectral norm at most `λ`.

**Formalization Note** The link at `0` is regular (Section 2.4), so its stationary measure is
uniform and `‖P_H|_{1^⊥}‖ ≤ λ` is `‖P_H f‖ ≤ λ ‖f‖` in the plain Euclidean norm on `ℝ^κ` for every
`f` with `∑ f = 0` ("for regular graphs we omit the subscript π", p.8). Connectivity of the link
is stated for the graph on its vertex set whose edges have positive weight. -/
theorem lemma_2_2 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {n : ℕ}
    (H : Matrix ι κ (ZMod 2)) (ρ : ℕ) (hH : IsGoodRelationMatrix H ρ)
    (φ : (κ → ZMod 2) →ₗ[ZMod 2] Vec n) (hφ : Function.Surjective φ)
    (hker : LinearMap.ker φ = rowspan H) (lam : ℝ)
    (hconn : ∀ u ∈ linkVerts (relationComplex H φ) 0, ∀ v ∈ linkVerts (relationComplex H φ) 0,
      Relation.ReflTransGen (fun a b => a ∈ linkVerts (relationComplex H φ) 0 ∧
        b ∈ linkVerts (relationComplex H φ) 0 ∧ 0 < linkWeight (relationComplex H φ) 0 a b) u v)
    (hnorm : ∀ f : κ → ℝ, ∑ i, f i = 0 →
      Real.sqrt (∑ i, ((PH H ρ).mulVec f i) ^ 2) ≤ lam * Real.sqrt (∑ i, f i ^ 2)) :
    HasLocalSpectralNorm (relationComplex H φ) lam := by sorry

end AbelianCayleyHDX
