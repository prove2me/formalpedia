-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_lemma_1
-- name    : DetSpectralSparsify.Dense.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:01.247919+00:00
-- url     : https://prove2.me/theorems/b094ab14-f61b-4a3e-8f69-bab912ce7d41
-- title:
--   Lemma 1 (Cheeger's inequality) — connectivity, kernel and spectrum of the normalized Laplacian
-- statement:
--   Let $G$ be a weighted multigraph with nonnegative weights in which every vertex has positive weighted degree, and let $\phi>0$ with $\Phi(G)\ge\phi$. Write $D_G^{1/2}\mathbf 1$ for the vector $(\sqrt{\deg_G(v)})_v$ and $U_G=(D_G^{1/2}\mathbf 1)^\perp$. Then
--
--   1. $G$ is connected;
--   2. $\ker\mathcal L_G=\mathrm{span}(D_G^{1/2}\mathbf 1)$;
--   3. on $U_G$,
--   $$\frac{\phi^2}{2}\,I_{U_G}\;\preceq\;\mathcal L_G\big|_{U_G}\;\preceq\;2\,I_{U_G}.$$
--
--   The bounds control the norm of $P=(\mathcal L_G|_U)^{-1/2}$ and the spectrum used to set $R=4\beta q/(\delta\phi^2)$ in the expander sparsifier.
--
--   **Formalization Note** Self-loops are allowed and count in degrees and volumes. The operator inequalities on $U_G$ are stated as quadratic-form inequalities $\tfrac{\phi^2}{2}\|x\|^2\le x^\top\mathcal L_Gx\le2\|x\|^2$ for every $x\perp D_G^{1/2}\mathbf 1$; the kernel statement is $\mathcal L_Gx=0\iff x\in\mathbb R\,D_G^{1/2}\mathbf 1$.
--
--   Differences from the source:
--   - generalization: weighted multigraph (positive weights) → nonnegative weights; reason: zero-weight self-loops occur in cluster graphs G⟨U⟩; positive weights are a special case
--   - encoding: standing convention 'we discard isolated vertices' (p.5), under which D_G^{-1/2} is defined → hypothesis deg_G(v) > 0 for every v; reason: 𝓛_G is undefined at a vertex of degree 0; the hypothesis excludes only that case
--   - encoding: Φ(G) ≥ ϕ with Φ(G) a minimum over cuts → `CondAtLeast G ϕ`: the inequality for every cut ∅ ≠ S ⊊ V; reason: equivalent for n ≥ 2; avoids a minimum over an empty family for n ≤ 1
--   - encoding: operator inequalities on U_G and ker 𝓛_G = span(D^{1/2}1) → quadratic-form inequalities for x ⊥ D^{1/2}1 and the solution set of 𝓛_G x = 0; reason: the same statements for the symmetric matrix 𝓛_G
--   - reading: G is connected → every cut ∅ ≠ S ⊊ V is crossed by an edge of positive weight; reason: with zero weights allowed, connectivity is through positive-weight edges, the stronger notion
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.5, Lemma 1

import Definitions.Def_DetSpectralSparsify_Dense_Multigraph

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense

/-- Lemma 1 (Cheeger's inequality), p.5. If `Φ(G) ≥ ϕ > 0` then `G` is connected,
`ker 𝓛_G = span(D_G^{1/2} 𝟏)`, and on `U_G = (D_G^{1/2} 𝟏)^⊥`,
`(ϕ²/2) I ⪯ 𝓛_G|_U ⪯ 2 I`. Weights are nonnegative and no vertex has degree `0`
(the standing convention "we discard isolated vertices"). -/
theorem lemma_1 {n : ℕ} (G : Multigraph n) (ϕ : ℝ)
    (hw : ∀ e, 0 ≤ G.w e) (hdeg : ∀ v, 0 < G.deg v)
    (hϕ : 0 < ϕ) (hΦ : G.CondAtLeast ϕ) :
    G.IsConnected ∧
    (∀ x : Fin n → ℝ, G.normLaplacian *ᵥ x = 0 ↔ ∃ c : ℝ, x = c • G.sqrtDegVec) ∧
    ∀ x : Fin n → ℝ, x ⬝ᵥ G.sqrtDegVec = 0 →
      ϕ ^ 2 / 2 * (x ⬝ᵥ x) ≤ x ⬝ᵥ (G.normLaplacian *ᵥ x) ∧
      x ⬝ᵥ (G.normLaplacian *ᵥ x) ≤ 2 * (x ⬝ᵥ x) := by sorry

end DetSpectralSparsify.Dense
