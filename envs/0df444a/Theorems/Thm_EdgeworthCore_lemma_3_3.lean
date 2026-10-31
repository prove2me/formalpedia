-- Prove2me | Theorems.Thm_EdgeworthCore_lemma_3_3
-- name    : EdgeworthCore.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:37.833658+00:00
-- url     : https://prove2.me/theorems/1a673c09-b110-4647-9bf7-6eb9c53d22d9
-- title:
--   Lemma 3.3 — $(-\delta)\mathbf 1\in\mathrm{cvh}(\bigcup_i Q_i^\eta)$ iff $(-\delta)\mathbf 1\in\mathrm{cvh}(\bigcup_i \widehat Q_i^\eta)$ (bounded hull)
-- statement:
--   Let $\mathcal E=((u_i,\omega_i))_{i\in[h]}$ be an exchange economy with $h\ge 1$ consumers and $\ell\ge 1$ goods whose utilities satisfy the standing assumptions of §2 with parameters $\alpha>0$, $\lambda\ge 0$, $r\ge 0$ and $\varepsilon>0$:
--
--   1. each $u_i$ is continuously differentiable, strictly monotonic, concave and $\lambda$-Lipschitz on $\mathbb R^\ell_+$;
--   2. each $u_i$ is $\alpha$-strongly concave on $\{x\in\mathbb R^\ell_+ : \|x-\omega_i\|\le r\}$, and $\alpha r^2\ge 2\varepsilon\lambda\ell/h+2$;
--   3. $u_i(x_i)\in[0,1)$ for every allocation $x$ of $\mathcal E$ and every $i$.
--
--   Let $\bar\eta\in(0,1)$ be such that $u_i(x_i)<1-\bar\eta$ for every allocation $x$ and every $i$. Put $\delta=\varepsilon/h$. Let $\bar y$ be an allocation of $\mathcal E$ and $\eta\in[0,\bar\eta)$, and define
--   $$Q_i^\eta=\{z\in\mathbb R^\ell : u_i(z+\omega_i)\ge u_i(\bar y_i)+\eta\},\qquad \widehat Q_i^\eta=Q_i^\eta\cap\Big\{z : \|z\|\le\sqrt{2(\lambda\ell\delta+1)/\alpha}\Big\}.$$
--   Then
--   $$(-\delta)\mathbf 1\in\mathrm{cvh}\Big(\bigcup_{i=1}^h Q_i^\eta\Big)\iff(-\delta)\mathbf 1\in\mathrm{cvh}\Big(\bigcup_{i=1}^h \widehat Q_i^\eta\Big).$$
--
--   The sets $Q_i^\eta$ are unbounded; the lemma says that the containment of $(-\delta)\mathbf 1$ in their convex hull can be witnessed by trades of norm at most $\sqrt{2(\lambda\ell\delta+1)/\alpha}$. This bound is what makes the coalition size in the main theorem independent of $n$.
--
--   **Formalization Note** Membership in $Q_i^\eta$ includes $z+\omega_i\in\mathbb R^\ell_+$ (footnote 11). Bundles are `EuclideanSpace ℝ (Fin ℓ)` and the ball is the closed Euclidean ball about $0$.
--
--   Differences from the source:
--   - reading: "strictly monotonic, continuously differentiable, and strongly concave utilities", λ the Lipschitz constant → all standing assumptions of §2 as hypotheses (concavity on ℝ^ℓ_+, λ-Lipschitz for the Euclidean norm, αr² ≥ 2ελℓ/h + 2, normalization [0,1) and [0,1−η̄)); reason: §2 states them once for the whole paper (pp.5, 7) and the proof uses them (p.9, footnotes 12–14, p.11)
--   - reading: parameter δ > 0 → δ = ε/h with ε > 0 and h ≥ 1; reason: §3.1 fixes δ := ε/h (p.9), and the radius condition αr² ≥ 2ελℓ/h + 2 ties r to this δ
--   - generalization: strong concavity on a set R containing every ball of radius r about an endowment → u_i strongly concave only on its own ball about ω_i, intersected with ℝ^ℓ_+; reason: every such R implies the Lean hypothesis; R = the union of the balls gives the page's case
--   - encoding: u_i : ℝ^ℓ_+ → ℝ with gradient ∇u_i → total function on EuclideanSpace ℝ (Fin ℓ), hypotheses only on ℝ^ℓ_+, gradient = derivative within ℝ^ℓ_+; reason: the orthant has unique derivatives, so the values on ℝ^ℓ_+ determine the gradient; same instances
--   - encoding: h consumers, ℓ goods → 0 < h and 0 < ℓ; reason: [h] and [ℓ] are nonempty in the paper; excludes only the degenerate cases where ε/h or the simplex is undefined
-- source:
--   Barman–Echenique, arXiv:1905.05165v1, §3.1, Lemma 3.3, p.9 (set-up of Q_i^η, Q̂_i^η and δ := ε/h on p.9; η̄ from Utility normalization, p.7; proof pp.9–11)

import Mathlib
import Definitions.Def_EdgeworthCore_Model

namespace EdgeworthCore

/-- **Lemma 3.3** (bounded hull; Barman–Echenique, arXiv:1905.05165v1, §3.1, p.9). Let `E` be an
economy with `h ≥ 1` consumers and `ℓ ≥ 1` goods satisfying the standing assumptions of §2 with
parameters `α, λ, r, ε` (`ε > 0`), and let `η̄ ∈ (0, 1)` be such that `u_i(x_i) < 1 − η̄` for every
allocation `x` of `E` and every `i` (p.7). Put `δ := ε/h`. Let `y` be an allocation of `E` and
`η ∈ [0, η̄)`. With `Q_i^η = {z | u_i(z + ω_i) ≥ u_i(y_i) + η}` and
`Q̂_i^η = Q_i^η ∩ {z : ‖z‖ ≤ √(2(λℓδ + 1)/α)}`,

`(−δ)1 ∈ cvh(⋃_i Q_i^η)  ↔  (−δ)1 ∈ cvh(⋃_i Q̂_i^η)`.

**Formalization Note.** `Q_i^η` is `tradeSet E y η i` (its membership includes `z + ω_i ∈ ℝ^ℓ_+`,
footnote 11); `Q̂_i^η` is its intersection with the closed Euclidean ball of radius
`√(2(λℓδ + 1)/α)` about `0`. The page's "`δ > 0`" follows from `ε > 0` and `h ≥ 1`, and the
radius condition `αr² ≥ 2ελℓ/h + 2` of the standing assumptions ties `r` to `δ = ε/h`. -/
theorem lemma_3_3 {h ℓ : ℕ} (hh : 0 < h) (hℓ : 0 < ℓ) (E : Economy (Fin h) ℓ)
    (α lam r ε : ℝ) (hε : 0 < ε) (hE : StandingAssumptions E α lam r ε)
    (ηbar : ℝ) (hηbar_pos : 0 < ηbar) (hηbar_lt : ηbar < 1)
    (hnorm : ∀ x : Fin h → Bundle ℓ, IsAllocation E x → ∀ i, E.u i (x i) < 1 - ηbar)
    (y : Fin h → Bundle ℓ) (hy : IsAllocation E y) (η : ℝ) (hη_nonneg : 0 ≤ η)
    (hη_lt : η < ηbar) :
    (-(ε / h)) • ones ℓ ∈ convexHull ℝ (⋃ i, tradeSet E y η i) ↔
      (-(ε / h)) • ones ℓ ∈ convexHull ℝ (⋃ i, tradeSet E y η i ∩
        Metric.closedBall 0 (Real.sqrt (2 * (lam * ℓ * (ε / h) + 1) / α))) := by sorry

end EdgeworthCore
