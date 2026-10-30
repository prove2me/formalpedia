-- Prove2me | Theorems.Thm_CompOT_SinkhornConv_sinkhorn_one_step_contraction
-- name    : CompOT.SinkhornConv.sinkhorn_one_step_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:22:59.338382+00:00
-- url     : https://prove2.me/theorems/793c9153-e7ae-467e-8ae2-9cf7e2c560db
-- title:
--   Proof of Theorem 4.2: one Sinkhorn step contracts $d_{\mathcal H}$ by $\lambda(K)$
-- statement:
--   Let $a\in\Sigma_n$ and $b\in\Sigma_m$ be histograms with positive entries, let $C\in\mathbb R^{n\times m}$ be any cost matrix, $\varepsilon>0$, $K = e^{-C/\varepsilon}$ the Gibbs kernel and $\lambda(K)$ Birkhoff's contraction ratio. Let $(u^{(\ell)}, v^{(\ell)})$ be a run of Sinkhorn's iterations (4.15) started from $v^{(0)} = \mathbb 1_m$, and let $u^\star, v^\star$ be vectors with positive entries solving the scaling equations (4.14),
--   $$u^\star\odot(Kv^\star) = a, \qquad v^\star\odot(K^\top u^\star) = b.$$
--   Then for every $\ell\ge 0$,
--   $$d_{\mathcal H}(u^{(\ell+1)}, u^\star) \le \lambda(K)\, d_{\mathcal H}(v^{(\ell)}, v^\star), \qquad d_{\mathcal H}(v^{(\ell+1)}, v^\star) \le \lambda(K)\, d_{\mathcal H}(u^{(\ell+1)}, u^\star).$$
--
--   The paper derives the first inequality as $d_{\mathcal H}(u^{(\ell+1)},u^\star) = d_{\mathcal H}(a/(Kv^{(\ell)}), a/(Kv^\star)) = d_{\mathcal H}(Kv^{(\ell)}, Kv^\star)$ followed by Theorem 4.1; the second is the same step for the $v$-update, with $K^\top$ in place of $K$ (note $\lambda(K^\top) = \lambda(K)$). Chained, they give the rate $\lambda(K)^2$ per iteration in (4.22).
--
--   Differences from the source:
--   - reading: a ∈ Σ_n, b ∈ Σ_m (zero entries allowed) → a, b with positive entries; reason: d_H is defined only on positive vectors; with a zero entry in a or b the iterates have zero entries and every d_H in the statement is undefined
--   - generalization: (u⋆, v⋆) the limit of the iterates (Theorem 4.2) → (u⋆, v⋆) any positive solution of the scaling equations (4.14); reason: the limit is such a solution, so the statement specializes to the paper's; (4.14) is a genuine constraint, fixing (u⋆, v⋆) up to (r u⋆, v⋆/r)
--   - generalization: the printed chain for the u-update only → both the u-update inequality and the transposed v-update inequality; reason: the paper uses the v-update step without printing it when it concludes "This shows (4.22)"; the added clause only adds content
-- source:
--   Peyré, Cuturi, Computational Optimal Transport, Found. Trends Mach. Learn. 11(5–6) (2019), doi:10.1561/2200000073, §4.2, proof of Theorem 4.2, unnumbered display, p. 442

import Mathlib
import Definitions.Def_CompOT_SinkhornConv_hilbertDist
import Definitions.Def_CompOT_SinkhornConv_birkhoffLambda
import Definitions.Def_CompOT_SinkhornConv_gibbsKernel
import Definitions.Def_CompOT_SinkhornConv_IsSinkhornRun

open Matrix

namespace CompOT.SinkhornConv

/-- **One Sinkhorn step contracts `d_H` to a scaling solution by `λ(K)`.**
Peyré, Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11(5–6) (2019), §4.2, proof of Theorem 4.2, unnumbered display, p. 442: "This shows that
dH(u(ℓ+1), u⋆) = dH(a/(Kv(ℓ)), a/(Kv⋆)) = dH(Kv(ℓ), Kv⋆) ≤ λ(K)dH(v(ℓ), v⋆), where we used
Theorem 4.1. This shows (4.22)."

Let `a ∈ Σ_n`, `b ∈ Σ_m` have positive entries, `C` be any real cost, `ε > 0`, `K = e^{−C/ε}`,
and `(u^(ℓ), v^(ℓ))` a run of Sinkhorn's iterations (4.15) from `v^(0) = 1_m`. Let `(u⋆, v⋆)` be
positive vectors solving the scaling equations (4.14), `u⋆ ⊙ (K v⋆) = a` and
`v⋆ ⊙ (Kᵀ u⋆) = b`. Then for every `ℓ ≥ 0`,
`d_H(u^(ℓ+1), u⋆) ≤ λ(K) d_H(v^(ℓ), v⋆)` and `d_H(v^(ℓ+1), v⋆) ≤ λ(K) d_H(u^(ℓ+1), u⋆)`.

**Formalization Note.** `(u⋆, v⋆)` is any positive solution of (4.14), not specifically the
limit of the iterates: the inequalities hold for every such pair (the limit included), and (4.14)
is a genuine constraint (it determines `(u⋆, v⋆)` up to `(r u⋆, v⋆/r)`). The second inequality is
the transposed step (Theorem 4.1 applied to `Kᵀ`, with `λ(Kᵀ) = λ(K)`), which the paper uses
without printing it when it concludes "This shows (4.22)". -/
theorem sinkhorn_one_step_contraction {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 < a i) (ha1 : ∑ i, a i = 1) (hb : ∀ j, 0 < b j) (hb1 : ∑ j, b j = 1)
    {C : Matrix (Fin n) (Fin m) ℝ} {ε : ℝ} (hε : 0 < ε)
    {u : ℕ → Fin n → ℝ} {v : ℕ → Fin m → ℝ} (hrun : IsSinkhornRun (gibbsKernel C ε) a b u v)
    {ustar : Fin n → ℝ} {vstar : Fin m → ℝ} (hus : ∀ i, 0 < ustar i) (hvs : ∀ j, 0 < vstar j)
    (hfa : ustar * (gibbsKernel C ε *ᵥ vstar) = a)
    (hfb : vstar * ((gibbsKernel C ε)ᵀ *ᵥ ustar) = b) (ℓ : ℕ) :
    hilbertDist (u (ℓ + 1)) ustar ≤ birkhoffLambda (gibbsKernel C ε) * hilbertDist (v ℓ) vstar ∧
      hilbertDist (v (ℓ + 1)) vstar ≤
        birkhoffLambda (gibbsKernel C ε) * hilbertDist (u (ℓ + 1)) ustar := by sorry

end CompOT.SinkhornConv
