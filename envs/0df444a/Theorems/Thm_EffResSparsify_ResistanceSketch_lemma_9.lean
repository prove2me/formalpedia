-- Prove2me | Theorems.Thm_EffResSparsify_ResistanceSketch_lemma_9
-- name    : EffResSparsify.ResistanceSketch.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:35:08.153506+00:00
-- url     : https://prove2.me/theorems/813d17a4-5e3e-410a-b65a-bf63573457c2
-- title:
--   Lemma 9 — rows solved to $L$-norm accuracy $\delta$ preserve a $(1\pm\varepsilon)$ resistance sketch up to $(1\pm\varepsilon)^2$
-- statement:
--   Let $G=(V,E,w)$ be a connected simple weighted graph on $n$ vertices, with Laplacian $L$ and effective resistances $R_{uv}=(\chi_u-\chi_v)^{\mathsf T}L^+(\chi_u-\chi_v)$. Let $0<w_{\min}$ and $w_{\max}$ be real numbers with $w_{\min}\le w_e\le w_{\max}$ for every edge $e$, and let $0<\varepsilon<1$. Let $Z$ and $\widetilde Z$ be real $k\times n$ matrices (columns indexed by $V$) with rows $z_i$ and $\tilde z_i$, viewed as vectors in $\mathbb R^V$, and let $\delta$ be a real number. Suppose that
--
--   1. for every pair $u,v\in V$,
--   $$(1-\varepsilon)R_{uv}\le\|Z(\chi_u-\chi_v)\|^2\le(1+\varepsilon)R_{uv};$$
--   2. for every row index $i$, $\|z_i-\tilde z_i\|_L\le\delta\|z_i\|_L$, where $\|y\|_L=\sqrt{y^{\mathsf T}Ly}$; and
--   3. $$\delta\le\frac{\varepsilon}{3}\sqrt{\frac{2(1-\varepsilon)w_{\min}}{(1+\varepsilon)n^3w_{\max}}}.$$
--
--   Then for every pair $u,v\in V$,
--   $$
--   (1-\varepsilon)^2R_{uv}\ \le\ \|\widetilde Z(\chi_u-\chi_v)\|^2\ \le\ (1+\varepsilon)^2R_{uv}.
--   $$
--   Here $\|\cdot\|$ is the Euclidean norm on $\mathbb R^k$.
--
--   In the paper, $Z=QW^{1/2}BL^+$ is a Johnson–Lindenstrauss projection of the vectors $W^{1/2}BL^+\chi_v$, whose pairwise squared distances are the effective resistances, and $\tilde z_i$ is the output of an approximate Laplacian solver applied to the $i$-th row of $QW^{1/2}B$. The lemma says that solving each of the $k$ systems only to relative $L$-norm accuracy $\delta$ still gives a sketch $\widetilde Z$ from which every effective resistance can be read off to within a factor $(1\pm\varepsilon)^2$. It is the correctness half of the paper's Theorem 2 (nearly-linear-time approximation of all effective resistances).
--
--   **Formalization Note** The lemma holds for arbitrary $k$, $Z$, $\widetilde Z$ satisfying the hypotheses, which is how it is stated here; the paper's specific $Z$ and solver output are instances. The paper's $w_{\min}$ and $w_{\max}$ are the smallest and largest edge weights; here they are any bounds $0<w_{\min}\le w_e\le w_{\max}$, of which the exact extremes are an instance. The paper fixes no range for $\varepsilon$; $0<\varepsilon<1$ is assumed because for $\varepsilon\ge1$ the square root in condition 3 has a non-positive argument. The graph is assumed simple because the paper's proof uses Proposition 10, which fails for multigraphs.
-- source:
--   Spielman, Srivastava, Graph Sparsification by Effective Resistances, arXiv:0803.0929v4, p. 11, Lemma 9 (with (4), (5)); proof pp. 11–12

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph

namespace EffResSparsify.ResistanceSketch

open Matrix

/-- Lemma 9 (p. 11): let `G` be a connected simple weighted graph on `n` vertices with edge
weights in `[wmin, wmax]`, `0 < wmin`, and let `0 < ε < 1`. Let `Z, Z̃` be `k × n` matrices
with rows `z_i, z̃_i`. If `(1 − ε) R_uv ≤ ‖Z(χ_u − χ_v)‖² ≤ (1 + ε) R_uv` for every pair
`u, v`, if `‖z_i − z̃_i‖_L ≤ δ ‖z_i‖_L` for all `i` (4), and if
`δ ≤ (ε/3) √(2(1 − ε) wmin / ((1 + ε) n³ wmax))` (5), then
`(1 − ε)² R_uv ≤ ‖Z̃(χ_u − χ_v)‖² ≤ (1 + ε)² R_uv` for every pair `u, v`. -/
theorem lemma_9 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : WGraph V E) (hconn : G.IsConnected) (hsimple : G.IsSimple)
    (wmin wmax : ℝ) (hwmin : 0 < wmin) (hw : ∀ e, wmin ≤ G.w e ∧ G.w e ≤ wmax)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (k : ℕ) (Z Zt : Matrix (Fin k) V ℝ) (δ : ℝ)
    (hZ : ∀ u v : V,
      (1 - ε) * G.R u v ≤ sqNorm (Z *ᵥ (WGraph.chi u - WGraph.chi v)) ∧
        sqNorm (Z *ᵥ (WGraph.chi u - WGraph.chi v)) ≤ (1 + ε) * G.R u v)
    (h4 : ∀ i : Fin k, G.lNorm (Z i - Zt i) ≤ δ * G.lNorm (Z i))
    (h5 : δ ≤ ε / 3 * Real.sqrt (2 * (1 - ε) * wmin /
      ((1 + ε) * (Fintype.card V : ℝ) ^ 3 * wmax))) :
    ∀ u v : V,
      (1 - ε) ^ 2 * G.R u v ≤ sqNorm (Zt *ᵥ (WGraph.chi u - WGraph.chi v)) ∧
        sqNorm (Zt *ᵥ (WGraph.chi u - WGraph.chi v)) ≤ (1 + ε) ^ 2 * G.R u v := by sorry

end EffResSparsify.ResistanceSketch
