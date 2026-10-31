-- Prove2me | Theorems.Thm_CompositeSAA_composite_tendstoUniformlyOn
-- name    : CompositeSAA.composite_tendstoUniformlyOn
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:57.298628+00:00
-- url     : https://prove2.me/theorems/24536b3b-9e3d-4a4d-a9eb-0f67ec628112
-- title:
--   Proof of Theorem 3, p.6 — uniform convergence of the levels gives uniform convergence of the composite (corrected: limit levels continuous)
-- statement:
--   Let $\mathcal U\subseteq\mathbb R^n$ and $I_1,\dots,I_k$ ($k\ge1$, $I_j\subseteq\mathbb R^{m_j}$, $m_0=1$) be compact. Let $\bar g_j(u,\eta)\in\mathbb R^{m_{j-1}}$ ($j=1,\dots,k$) be continuous on $\mathcal U\times I_j$ and $\bar g_{k+1}(u)\in\mathbb R^{m_k}$ continuous on $\mathcal U$, with
--
--   $$
--   \bar g_{j+1}(\mathcal U,I_{j+1})\subseteq\operatorname{int}(I_j)\ (j=1,\dots,k-1),\qquad \bar g_{k+1}(\mathcal U)\subseteq\operatorname{int}(I_k).
--   $$
--
--   If $h^N_j\to\bar g_j$ uniformly on $\mathcal U\times I_j$ ($j\le k$) and $h^N_{k+1}\to\bar g_{k+1}$ uniformly on $\mathcal U$, then
--
--   $$
--   h^N_1\bigl(u,h^N_2(u,\cdots h^N_k(u,h^N_{k+1}(u))\cdots)\bigr)\ \longrightarrow\ \bar g_1\bigl(u,\bar g_2(u,\cdots\bar g_k(u,\bar g_{k+1}(u))\cdots)\bigr)
--   $$
--
--   uniformly in $u\in\mathcal U$.
--
--   This is the step of the proof of Theorem 3 that passes from convergence of each level's integrals, $h^N_j=\bar f^{Q^j_N}_j$, to convergence of the composite objective $\varrho^{(Q_N)}[u,X]\to\varrho[u,X]$.
--
--   Differences from the source:
--   - correction: "the continuity of the functions $f_j$ with respect to their second argument implies" the convergence → the limit level maps $\bar g_j$ are assumed continuous on $\mathcal U\times I_j$; reason: continuity of $f_j(u,\cdot,x)$ for each $x$ does not make $\bar f^P_j$ continuous (a unit-mass tent $T(\eta,x)$ on $[0,2(\eta-\tfrac12)]$ is continuous in $\eta$ for each $x$, yet $\int_0^1T(\eta,x)\,dx$ jumps from $0$ to $1$ at $\eta=\tfrac12$), and with $h^N_2=\tfrac12+\tfrac1{2N}\to\bar g_2=\tfrac12$ uniformly the composite stays $1$ above its limit.
--   - generalization: the level maps $\bar f^{Q^j_N}_j\to\bar f^P_j$ → arbitrary level maps $h^N_j\to\bar g_j$; reason: the paper's maps are an instance.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, proof of Theorem 3, p.6

import Mathlib
import Definitions.Def_CompositeSAA_nestedComposite

open Filter Topology

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, proof of Theorem 3, p.6 (the composition step):
uniform convergence of the level maps on `𝒰 × I_j` gives uniform convergence of the nested
composite on `𝒰`.

Let `𝒰 ⊆ ℝ^n` and `I_1, …, I_k` (`k ≥ 1`) be compact, and let `ḡ_j` (`j = 1, …, k`) be level maps
continuous on `𝒰 × I_j`, and `ḡ_{k+1}` continuous on `𝒰`, with `ḡ_{j+1}(𝒰, I_{j+1}) ⊆ int(I_j)`
(`j = 1, …, k − 1`) and `ḡ_{k+1}(𝒰) ⊆ int(I_k)`. If `h^N_j → ḡ_j` uniformly on `𝒰 × I_j`
(`j = 1, …, k`) and `h^N_{k+1} → ḡ_{k+1}` uniformly on `𝒰`, then
`h^N_1(u, h^N_2(u, ⋯ h^N_{k+1}(u) ⋯)) → ḡ_1(u, ḡ_2(u, ⋯ ḡ_{k+1}(u) ⋯))` uniformly on `𝒰`.

**Formalization Note** Stated for arbitrary level maps; the paper applies it with
`h^N_j = f̄^{Q^j_N}_j` and `ḡ_j = f̄^P_j`. The continuity of the limit level maps on `𝒰 × I_j` is
the corrected hypothesis: the paper credits the continuity of `f_j` in its second argument, which
does not give it. -/
theorem composite_tendstoUniformlyOn {m : ℕ → ℕ} (hm : m 0 = 1) {k n : ℕ} (hk : 1 ≤ k)
    (𝒰 : Set (EuclideanSpace ℝ (Fin n))) (I : (j : ℕ) → Set (EuclideanSpace ℝ (Fin (m j))))
    (h𝒰 : IsCompact 𝒰) (hI : ∀ j, 1 ≤ j → j ≤ k → IsCompact (I j))
    (g : (j : ℕ) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m j)) →
      EuclideanSpace ℝ (Fin (m (j - 1))))
    (gTop : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m k)))
    (hg : ∀ j, 1 ≤ j → j ≤ k →
      ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin (m j)) =>
        g j p.1 p.2) (𝒰 ×ˢ I j))
    (hgTop : ContinuousOn gTop 𝒰)
    (hint : ∀ j, 1 ≤ j → j < k → ∀ u ∈ 𝒰, ∀ η ∈ I (j + 1), g (j + 1) u η ∈ interior (I j))
    (hintTop : ∀ u ∈ 𝒰, gTop u ∈ interior (I k))
    (h : ℕ → (j : ℕ) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m j)) →
      EuclideanSpace ℝ (Fin (m (j - 1))))
    (hTop : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m k)))
    (hconv : ∀ j, 1 ≤ j → j ≤ k →
      TendstoUniformlyOn
        (fun N (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin (m j))) => h N j p.1 p.2)
        (fun p => g j p.1 p.2) atTop (𝒰 ×ˢ I j))
    (hconvTop : TendstoUniformlyOn hTop gTop atTop 𝒰) :
    TendstoUniformlyOn (fun N => nestedComposite m hm k n (h N) (hTop N))
      (nestedComposite m hm k n g gTop) atTop 𝒰 := by sorry

end CompositeSAA
