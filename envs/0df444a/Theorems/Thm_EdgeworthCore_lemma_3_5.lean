-- Prove2me | Theorems.Thm_EdgeworthCore_lemma_3_5
-- name    : EdgeworthCore.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:55.587381+00:00
-- url     : https://prove2.me/theorems/3b6b65de-bace-460c-9bea-db1f10297b79
-- title:
--   Lemma 3.5 — for a $\kappa$-core allocation of $\mathcal E^n$, $(-\delta)\mathbf 1\notin\mathrm{cvh}(\bigcup_i P_i^\eta)$
-- statement:
--   Let $\mathcal E=((u_i,\omega_i))_{i\in[h]}$ be an exchange economy with $h\ge 1$ consumers and $\ell\ge 1$ goods whose utilities satisfy the standing assumptions of §2 with parameters $\alpha>0$, $\lambda\ge 0$, $r\ge 0$ and $\varepsilon>0$ (continuously differentiable, strictly monotonic, concave and $\lambda$-Lipschitz on $\mathbb R^\ell_+$; $\alpha$-strongly concave on the ball of radius $r$ about each endowment with $\alpha r^2\ge 2\varepsilon\lambda\ell/h+2$; $u_i(x_i)\in[0,1)$ on allocations of $\mathcal E$). Put
--   $$\delta=\frac{\varepsilon}{h},\qquad\gamma=\sqrt{\frac{2(\lambda\ell\delta+1)}{\alpha}},$$
--   and let $n\ge\kappa\ge 8\gamma^2/\delta^2$. Let $\bar x$ be an allocation of $\mathcal E$ whose $n$-times replicated version belongs to the $\kappa$-core of the replica economy $\mathcal E^n$. Let $\bar\eta>0$ with $u_i(\bar x_i)\in[0,1-\bar\eta]$ for all $i$, let $\eta\in(0,\bar\eta)$, and put
--   $$P_i^\eta=\{z\in\mathbb R^\ell : u_i(z+\omega_i)\ge u_i(\bar x_i)+\eta\}.$$
--   Then
--   $$(-\delta)\mathbf 1\notin\mathrm{cvh}\Big(\bigcup_{i=1}^h P_i^\eta\Big).$$
--
--   Under a $\kappa$-core allocation, trades that make each consumer strictly better off cannot be combined across consumers into a net withdrawal of $\delta$ of every good. A separating hyperplane between $(-\delta)\mathbf 1$ and this hull is the price vector of the main theorem.
--
--   **Formalization Note** Membership in $P_i^\eta$ includes $z+\omega_i\in\mathbb R^\ell_+$. The bound $8\gamma^2/\delta^2$ equals $(16/\alpha)(\lambda\ell h/\varepsilon+h^2/\varepsilon^2)$, the bound of Theorem 3.2.
--
--   Differences from the source:
--   - reading: the printed lemma lists no hypotheses beyond "an allocation x̄ in the κ-core of E^n" → the set-up of §3.2 (δ = ε/h, γ, n ≥ κ ≥ 8γ²/δ², η̄ > 0 with u_i(x̄_i) ∈ [0, 1−η̄], η ∈ (0, η̄)) and the standing assumptions of §2 as hypotheses; reason: §3.2 opens with "Recall the notation from Theorem 3.2" and fixes these objects (p.12); the standing assumptions are stated once in §2 (pp.5, 7)
--   - reading: "allocation x̄ = (x̄_i)_{i∈[h]} that belongs to the κ-core of E^n" → the n-times replicated version of the allocation x̄ of E lies in the κ-core of E^n; reason: the paper's convention for κ-core allocations as vectors in ℝ^{hℓ}_+ (pp.7–8, footnote 10)
--   - generalization: strong concavity on a set R containing every ball of radius r about an endowment → u_i strongly concave only on its own ball about ω_i, intersected with ℝ^ℓ_+; reason: every such R implies the Lean hypothesis; R = the union of the balls gives the page's case
--   - generalization: normalization u_i(x_i) ∈ [0, 1−η̄) on allocations for some η̄ ∈ (0,1) (p.7) → u_i(x_i) ∈ [0,1) on allocations; reason: a weaker hypothesis that is the paper's own first form; by compactness of the set of allocations and continuity it implies the second form, so it specializes to the source
--   - encoding: u_i : ℝ^ℓ_+ → ℝ with gradient ∇u_i → total function on EuclideanSpace ℝ (Fin ℓ), hypotheses only on ℝ^ℓ_+, gradient = derivative within ℝ^ℓ_+; reason: the orthant has unique derivatives, so the values on ℝ^ℓ_+ determine the gradient; same instances
--   - encoding: S-allocation (y_i)_{i∈S} with no stated sign → y_i ∈ ℝ^ℓ_+; reason: u_i(y_i) is defined only on ℝ^ℓ_+ (p.5)
--   - encoding: h consumers, ℓ goods → 0 < h and 0 < ℓ; reason: [h] and [ℓ] are nonempty in the paper; excludes only the degenerate cases where ε/h or the simplex is undefined
-- source:
--   Barman–Echenique, arXiv:1905.05165v1, §3.2, Lemma 3.5, p.12 (set-up δ, γ, 8γ²/δ², η̄, U_i^η, P_i^η on p.12; proof pp.12–13)

import Mathlib
import Definitions.Def_EdgeworthCore_Model

namespace EdgeworthCore

/-- **Lemma 3.5** (no combination of beneficial trades; Barman–Echenique, arXiv:1905.05165v1,
§3.2, p.12). Let `E` be an economy with `h ≥ 1` consumers and `ℓ ≥ 1` goods satisfying the standing
assumptions of §2 with parameters `α, λ, r, ε` (`ε > 0`). Put `δ := ε/h` and
`γ := √(2(λℓδ + 1)/α)`, and let `n ≥ κ ≥ 8γ²/δ²` (the bound of Theorem 3.2, p.12). Let `x` be an
allocation of `E` whose `n`-fold replication lies in the κ-core of `E^n`, let `η̄ > 0` with
`u_i(x_i) ∈ [0, 1 − η̄]` for all `i`, and `η ∈ (0, η̄)`. With
`P_i^η = {z | u_i(z + ω_i) ≥ u_i(x_i) + η}`,

`(−δ)1 ∉ cvh(⋃_i P_i^η)`.

**Formalization Note.** The printed lemma lists none of these hypotheses; they are the set-up of
§3.2 ("Recall the notation from Theorem 3.2", p.12). `P_i^η` is `tradeSet E x η i` (definition of
p.12, with the margin `η`; membership includes `z + ω_i ∈ ℝ^ℓ_+`). The κ-core allocation
`x ∈ ℝ^{hℓ}_+` of `E^n` is the replicated allocation (pp.7–8, footnote 10). -/
theorem lemma_3_5 {h ℓ : ℕ} (hh : 0 < h) (hℓ : 0 < ℓ) (E : Economy (Fin h) ℓ)
    (α lam r ε : ℝ) (hε : 0 < ε) (hE : StandingAssumptions E α lam r ε)
    (x : Fin h → Bundle ℓ) (hx : IsAllocation E x) (n κ : ℕ) (hnκ : κ ≤ n)
    (hκ : 8 * Real.sqrt (2 * (lam * ℓ * (ε / h) + 1) / α) ^ 2 / (ε / h) ^ 2 ≤ (κ : ℝ))
    (hcore : InKappaCore (replica E n) κ (replicate n x))
    (ηbar : ℝ) (hηbar : 0 < ηbar) (hxbar : ∀ i, 0 ≤ E.u i (x i) ∧ E.u i (x i) ≤ 1 - ηbar)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < ηbar) :
    (-(ε / h)) • ones ℓ ∉ convexHull ℝ (⋃ i, tradeSet E x η i) := by sorry

end EdgeworthCore
