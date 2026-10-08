-- Prove2me | Theorems.Thm_CompOT_Sinkhorn_theorem_4_2
-- name    : CompOT.Sinkhorn.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:00.10499+00:00
-- url     : https://prove2.me/theorems/11f977bc-aa49-40cf-ae5a-dc66ad4352a7
-- title:
--   Theorem 4.2, p. 441 — Sinkhorn's iterates converge linearly in Hilbert's metric at rate λ(K)², with the a posteriori bounds (4.23) and (4.24)
-- statement:
--   Let $n, m \ge 1$, let $K \in \mathbb{R}^{n\times m}$, $a \in \mathbb{R}^n$ and $b \in \mathbb{R}^m$ have positive entries, and let $\lambda = \lambda(K) = \frac{\sqrt{\eta(K)}-1}{\sqrt{\eta(K)}+1}$ with $\eta(K) = \max_{i,j,k,\ell} \frac{K_{i,k}K_{j,\ell}}{K_{j,k}K_{i,\ell}}$. Let $(u^{(\ell)}, v^{(\ell)})$ be the iterates of Sinkhorn's algorithm
--   $$v^{(0)} = \mathbb{1}_m,\qquad u^{(\ell+1)} = \frac{a}{Kv^{(\ell)}},\qquad v^{(\ell+1)} = \frac{b}{K^\top u^{(\ell+1)}},$$
--   and let $(u^\star, v^\star)$ be vectors with positive entries solving $u^\star \odot (Kv^\star) = a$, $v^\star \odot (K^\top u^\star) = b$. Write $d_{\mathcal H}$ for Hilbert's projective metric, $P^{(\ell)} = \mathrm{diag}(u^{(\ell)})K\,\mathrm{diag}(v^{(\ell)})$ and $P^\star = \mathrm{diag}(u^\star)K\,\mathrm{diag}(v^\star)$. Then:
--
--   1. **Linear rate (4.22).** For every $\ell \ge 0$, $d_{\mathcal H}(v^{(\ell)}, v^\star) \le \lambda^{2\ell}\, d_{\mathcal H}(\mathbb{1}_m, v^\star)$, and for every $\ell \ge 1$, $d_{\mathcal H}(u^{(\ell)}, u^\star) \le \lambda^{2\ell-1}\, d_{\mathcal H}(\mathbb{1}_m, v^\star)$.
--   2. **Convergence.** $d_{\mathcal H}(u^{(\ell)}, u^\star) \to 0$ and $d_{\mathcal H}(v^{(\ell)}, v^\star) \to 0$ as $\ell \to \infty$.
--   3. **A posteriori bounds (4.23).** For every $\ell \ge 1$,
--   $$d_{\mathcal H}(u^{(\ell)}, u^\star) \le \frac{d_{\mathcal H}(P^{(\ell)}\mathbb{1}_m,\ a)}{1-\lambda^2},$$
--   and for every $\ell \ge 0$,
--   $$d_{\mathcal H}(v^{(\ell)}, v^\star) \le \frac{d_{\mathcal H}\big((\mathrm{diag}(u^{(\ell+1)})K\,\mathrm{diag}(v^{(\ell)}))^\top\mathbb{1}_n,\ b\big)}{1-\lambda^2}.$$
--   4. **Couplings (4.24).** For every $\ell \ge 1$,
--   $$\max_{i,j} \big|\log P^{(\ell)}_{i,j} - \log P^\star_{i,j}\big| \le d_{\mathcal H}(u^{(\ell)}, u^\star) + d_{\mathcal H}(v^{(\ell)}, v^\star).$$
--
--   This is the global linear convergence of Sinkhorn's algorithm (Franklin and Lorenz, 1989): each iteration contracts the distance of the scalings to the solution by $\lambda(K)^2 < 1$, and the marginal violations of the current coupling give computable stopping criteria.
--
--   **Formalization Note** (i) The book writes (4.22) as $O(\lambda(K)^{2\ell})$; its proof yields the constants stated here, $d_{\mathcal H}(v^{(0)}, v^\star)$ for $v$ and $d_{\mathcal H}(v^{(0)}, v^\star)$ with exponent $2\ell - 1$ for $u$. (ii) The book's "$(u^{(\ell)}, v^{(\ell)}) \to (u^\star, v^\star)$" is stated in its projective form ($d_{\mathcal H} \to 0$), which is what the proof establishes; scalings are only defined up to $(ru, v/r)$. (iii) As printed, the second inequality of (4.23) uses $P^{(\ell),\top}\mathbb{1}_n = v^{(\ell)} \odot (K^\top u^{(\ell)})$, which equals $b$ for every $\ell \ge 1$ by (4.15), so its right side is $0$ and the printed inequality is false; the statement here uses the half-step coupling that the mirrored proof ("the second one being similar") produces. (iv) In (4.24), $P^\star$ is taken as $\mathrm{diag}(u^\star)K\,\mathrm{diag}(v^\star)$, which by Proposition 4.3 is the unique solution of (4.2); $\|\cdot\|_\infty$ is the entrywise maximum norm. The book cites (4.24) to Franklin–Lorenz, Lemma 3, without proof. (v) The book's histograms lie in the probability simplex; only positivity and the existence of a positive solution $(u^\star, v^\star)$ (which forces $\sum_i a_i = \sum_j b_j$) are used. (vi) Iterates $u^{(\ell)}$ exist only for $\ell \ge 1$; $u^{(0)}$ is unconstrained and only enters the limit statement. Indices are $0$-based.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Remark 4.14, Theorem 4.2, (4.22)–(4.24), p. 441, and its proof, pp. 441–442

import Mathlib
import Definitions.Def_CompOT_Sinkhorn_Defs

namespace CompOT.Sinkhorn

open Matrix Filter Topology

/-- Theorem 4.2 (Franklin–Lorenz), Remark 4.14, p. 441, with the explicit constants of
the book's proof in place of the `O(·)` of (4.22), and the second inequality of (4.23)
stated with the half-step coupling `diag(u^{(ℓ+1)}) K diag(v^{(ℓ)})` (as printed, with
`P^{(ℓ)}`, its right side is `0` for `ℓ ≥ 1`). Here `P⋆ = diag(u⋆) K diag(v⋆)`.
Iterates `u^{(ℓ)}` exist only for `ℓ ≥ 1`. -/
theorem theorem_4_2 {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (b : Fin m → ℝ) (hb : ∀ j, 0 < b j)
    (u : ℕ → Fin n → ℝ) (v : ℕ → Fin m → ℝ) (hrun : IsSinkhornRun K a b u v)
    (us : Fin n → ℝ) (vs : Fin m → ℝ) (hus : ∀ i, 0 < us i) (hvs : ∀ j, 0 < vs j)
    (hsol : IsScalingSolution K a b us vs) :
    -- (4.22), explicit: d_H(v^{(ℓ)}, v⋆) ≤ λ^{2ℓ} d_H(v^{(0)}, v⋆)
    (∀ ℓ : ℕ, hilbertMetric (v ℓ) vs ≤ lam K ^ (2 * ℓ) * hilbertMetric (v 0) vs) ∧
    -- (4.22), explicit: d_H(u^{(ℓ+1)}, u⋆) ≤ λ^{2ℓ+1} d_H(v^{(0)}, v⋆)
    (∀ ℓ : ℕ, hilbertMetric (u (ℓ + 1)) us ≤
      lam K ^ (2 * ℓ + 1) * hilbertMetric (v 0) vs) ∧
    -- projective convergence (u^{(ℓ)}, v^{(ℓ)}) → (u⋆, v⋆) in d_H
    Tendsto (fun ℓ => hilbertMetric (u ℓ) us) atTop (𝓝 0) ∧
    Tendsto (fun ℓ => hilbertMetric (v ℓ) vs) atTop (𝓝 0) ∧
    -- (4.23), first part as printed, for ℓ ≥ 1
    (∀ ℓ : ℕ, 1 ≤ ℓ → hilbertMetric (u ℓ) us ≤
      hilbertMetric (scaledCoupling (u ℓ) K (v ℓ) *ᵥ 1) a / (1 - lam K ^ 2)) ∧
    -- (4.23), second part, with the half-step coupling diag(u^{(ℓ+1)}) K diag(v^{(ℓ)})
    (∀ ℓ : ℕ, hilbertMetric (v ℓ) vs ≤
      hilbertMetric ((scaledCoupling (u (ℓ + 1)) K (v ℓ))ᵀ *ᵥ 1) b / (1 - lam K ^ 2)) ∧
    -- (4.24), for ℓ ≥ 1, with P⋆ = diag(u⋆) K diag(v⋆)
    (∀ ℓ : ℕ, 1 ≤ ℓ →
      (⨆ i, ⨆ j, |Real.log (scaledCoupling (u ℓ) K (v ℓ) i j) -
          Real.log (scaledCoupling us K vs i j)|) ≤
        hilbertMetric (u ℓ) us + hilbertMetric (v ℓ) vs) := by sorry

end CompOT.Sinkhorn
