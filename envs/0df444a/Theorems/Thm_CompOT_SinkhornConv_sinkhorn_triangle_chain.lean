-- Prove2me | Theorems.Thm_CompOT_SinkhornConv_sinkhorn_triangle_chain
-- name    : CompOT.SinkhornConv.sinkhorn_triangle_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:23:37.367088+00:00
-- url     : https://prove2.me/theorems/f0899002-3786-48de-a646-49479e485b1a
-- title:
--   Proof of Theorem 4.2: $d_{\mathcal H}(u^{(\ell)},u^\star) \le d_{\mathcal H}(a, u^{(\ell)}\odot Kv^{(\ell)}) + \lambda(K)^2 d_{\mathcal H}(u^{(\ell)},u^\star)$
-- statement:
--   Let $a\in\Sigma_n$ and $b\in\Sigma_m$ be histograms with positive entries, let $C\in\mathbb R^{n\times m}$ be any cost matrix, $\varepsilon>0$, $K = e^{-C/\varepsilon}$ the Gibbs kernel and $\lambda(K)$ Birkhoff's contraction ratio. Let $(u^{(\ell)}, v^{(\ell)})$ be a run of Sinkhorn's iterations (4.15) started from $v^{(0)} = \mathbb 1_m$, and let $u^\star, v^\star$ be vectors with positive entries solving the scaling equations (4.14),
--   $$u^\star\odot(Kv^\star) = a, \qquad v^\star\odot(K^\top u^\star) = b.$$
--   Then for every $\ell\ge 1$,
--   $$d_{\mathcal H}(u^{(\ell)}, u^\star) \le d_{\mathcal H}\big(a,\ u^{(\ell)}\odot(Kv^{(\ell)})\big) + \lambda(K)^2\, d_{\mathcal H}(u^{(\ell)}, u^\star).$$
--
--   Since $u^{(\ell)}\odot(Kv^{(\ell)}) = P^{(\ell)}\mathbb 1_m$ is the row marginal of the current coupling $P^{(\ell)} = \mathrm{diag}(u^{(\ell)})K\mathrm{diag}(v^{(\ell)})$ and $\lambda(K)<1$, rearranging gives the first bound of (4.23): the distance of the scaling to its limit is controlled by the observable violation of the row constraint.
--
--   Differences from the source:
--   - reading: a ∈ Σ_n, b ∈ Σ_m (zero entries allowed) → a, b with positive entries; reason: d_H is defined only on positive vectors; with a zero entry in a or b the iterates have zero entries and every d_H in the statement is undefined
--   - reading: ℓ unrestricted → ℓ ≥ 1; reason: u^(0) is not defined by the iterations (4.15), and the step uses v^(ℓ) = b/(Kᵀu^(ℓ))
--   - generalization: (u⋆, v⋆) the limit of the iterates (Theorem 4.2) → (u⋆, v⋆) any positive solution of the scaling equations (4.14); reason: the limit is such a solution, so the statement specializes to the paper's; (4.14) is a genuine constraint, fixing (u⋆, v⋆) up to (r u⋆, v⋆/r)
-- source:
--   Peyré, Cuturi, Computational Optimal Transport, Found. Trends Mach. Learn. 11(5–6) (2019), doi:10.1561/2200000073, §4.2, proof of Theorem 4.2, unnumbered display, p. 442

import Mathlib
import Definitions.Def_CompOT_SinkhornConv_hilbertDist
import Definitions.Def_CompOT_SinkhornConv_birkhoffLambda
import Definitions.Def_CompOT_SinkhornConv_gibbsKernel
import Definitions.Def_CompOT_SinkhornConv_IsSinkhornRun

open Matrix

namespace CompOT.SinkhornConv

/-- **Triangle-inequality chain behind the first bound of (4.23).**
Peyré, Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11(5–6) (2019), §4.2, proof of Theorem 4.2, unnumbered display, p. 442: "One also has, using the
triangular inequality, dH(u(ℓ), u⋆) ≤ dH(u(ℓ+1), u(ℓ)) + dH(u(ℓ+1), u⋆)
≤ dH(a/(Kv(ℓ)), u(ℓ)) + λ(K)²dH(u(ℓ), u⋆) = dH(a, u(ℓ) ⊙ (Kv(ℓ))) + λ(K)²dH(u(ℓ), u⋆)".

With the hypotheses of the one-step contraction (positive `a ∈ Σ_n`, `b ∈ Σ_m`, any cost `C`,
`ε > 0`, a Sinkhorn run, and any positive solution `(u⋆, v⋆)` of (4.14)), for every `ℓ ≥ 1`,
`d_H(u^(ℓ), u⋆) ≤ d_H(a, u^(ℓ) ⊙ (K v^(ℓ))) + λ(K)² d_H(u^(ℓ), u⋆)`.

**Formalization Note.** Only the final line of the paper's chain is stated; the middle lines are
its proof. `ℓ ≥ 1` because `u^(0)` is not defined by the iterations (4.15). `(u⋆, v⋆)` is any
positive solution of (4.14), as in the one-step contraction. -/
theorem sinkhorn_triangle_chain {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 < a i) (ha1 : ∑ i, a i = 1) (hb : ∀ j, 0 < b j) (hb1 : ∑ j, b j = 1)
    {C : Matrix (Fin n) (Fin m) ℝ} {ε : ℝ} (hε : 0 < ε)
    {u : ℕ → Fin n → ℝ} {v : ℕ → Fin m → ℝ} (hrun : IsSinkhornRun (gibbsKernel C ε) a b u v)
    {ustar : Fin n → ℝ} {vstar : Fin m → ℝ} (hus : ∀ i, 0 < ustar i) (hvs : ∀ j, 0 < vstar j)
    (hfa : ustar * (gibbsKernel C ε *ᵥ vstar) = a)
    (hfb : vstar * ((gibbsKernel C ε)ᵀ *ᵥ ustar) = b) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    hilbertDist (u ℓ) ustar ≤
      hilbertDist a (u ℓ * (gibbsKernel C ε *ᵥ v ℓ)) +
        birkhoffLambda (gibbsKernel C ε) ^ 2 * hilbertDist (u ℓ) ustar := by sorry

end CompOT.SinkhornConv
