-- Prove2me | Theorems.Thm_EdgeworthCore_theorem_3_2
-- name    : EdgeworthCore.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:35.836759+00:00
-- url     : https://prove2.me/theorems/737433d5-0d64-4192-814c-c0decde9fb6f
-- title:
--   Theorem 3.2 (Main Result) — a $\kappa$-core allocation of $\mathcal E^n$, $n\ge\kappa\ge\frac{16}{\alpha}(\frac{\lambda\ell h}{\varepsilon}+\frac{h^2}{\varepsilon^2})$, is $\varepsilon$-Walrasian
-- statement:
--   Let $\mathcal E=((u_i,\omega_i))_{i\in[h]}$ be an exchange economy with $h\ge 1$ consumers and $\ell\ge 1$ goods, endowments $\omega_i\in\mathbb R^\ell_+$, and let $\varepsilon>0$. Assume the standing assumptions of §2 with parameters $\alpha>0$, $\lambda\ge0$, $r\ge0$:
--
--   1. each $u_i$ is continuously differentiable, strictly monotonic and concave on $\mathbb R^\ell_+$, and $\lambda$-Lipschitz there for the Euclidean norm;
--   2. each $u_i$ is $\alpha$-strongly concave near its endowment: for all $x,y\in\mathbb R^\ell_+$ with $\|x-\omega_i\|,\|y-\omega_i\|\le r$,
--   $$u_i(y)\le u_i(x)+\nabla u_i(x)^{\mathsf T}(y-x)-\frac{\alpha}{2}\|y-x\|^2,$$
--   and the radius satisfies $\alpha r^2\ge 2\varepsilon\lambda\ell/h+2$;
--   3. utilities are normalized on allocations of $\mathcal E$: $u_i(x_i)\in[0,1)$ for every allocation $x$ of $\mathcal E$ and every $i$.
--
--   Let $\bar x$ be an allocation of $\mathcal E$ whose $n$-times replicated version belongs to the $\kappa$-core of the replica economy $\mathcal E^n$, where
--   $$n\ge\kappa\ge\frac{16}{\alpha}\left(\frac{\lambda\ell h}{\varepsilon}+\frac{h^2}{\varepsilon^2}\right).$$
--   Then $\bar x$ is an $\varepsilon$-Walrasian allocation: there is a price vector $p\in\Delta$ such that for every consumer $i$,
--
--   1. $|p^{\mathsf T}\bar x_i-p^{\mathsf T}\omega_i|\le\varepsilon$, and
--   2. every bundle $y\in\mathbb R^\ell_+$ with $u_i(y)>u_i(\bar x_i)$ satisfies $p^{\mathsf T}y>p^{\mathsf T}\omega_i-\varepsilon/h$.
--
--   This is a non-asymptotic Debreu–Scarf core convergence theorem: the size $\kappa$ of the blocking coalitions needed to force approximately competitive outcomes depends on $h$, $\ell$, $1/\varepsilon$ and the curvature and Lipschitz parameters, but not on the replication factor $n$.
--
--   **Formalization Note** Bundles and prices are `EuclideanSpace ℝ (Fin ℓ)`; gradients are derivatives within $\mathbb R^\ell_+$. In condition 2 of the conclusion, $h$ is the number of consumers of $\mathcal E$ (not $nh$).
--
--   Differences from the source:
--   - reading: "an allocation x̄ ∈ ℝ^{hℓ}_+ belongs to the κ-core of E^n" → x̄ is an allocation of E and its n-times replicated version (i, t) ↦ x̄_t lies in the κ-core of E^n; reason: the paper's convention for κ-core allocations as vectors in ℝ^{hℓ}_+ (pp.7–8, footnote 10)
--   - reading: "strictly monotonic, continuously differentiable, and α-strongly concave", λ the Lipschitz constant → all standing assumptions of §2 as hypotheses (concavity on ℝ^ℓ_+, λ-Lipschitz for the Euclidean norm, αr² ≥ 2ελℓ/h + 2, normalization on allocations of E); reason: §2 states them once for the whole paper (pp.5, 7), and the theorem's sentence refers to them ("λ is the Lipschitz constant of the utilities")
--   - generalization: strong concavity on a set R containing every ball of radius r about an endowment → u_i strongly concave only on its own ball about ω_i, intersected with ℝ^ℓ_+; reason: every such R implies the Lean hypothesis; R = the union of the balls gives the page's case
--   - generalization: normalization u_i(x_i) ∈ [0, 1−η̄) on allocations for some η̄ ∈ (0,1) (p.7) → u_i(x_i) ∈ [0,1) on allocations; reason: a weaker hypothesis that is the paper's own first form; by compactness of the set of allocations and continuity it implies the second form, so it specializes to the source
--   - encoding: u_i : ℝ^ℓ_+ → ℝ with gradient ∇u_i → total function on EuclideanSpace ℝ (Fin ℓ), hypotheses only on ℝ^ℓ_+, gradient = derivative within ℝ^ℓ_+; reason: the orthant has unique derivatives, so the values on ℝ^ℓ_+ determine the gradient; same instances
--   - encoding: S-allocation (y_i)_{i∈S} with no stated sign → y_i ∈ ℝ^ℓ_+; reason: u_i(y_i) is defined only on ℝ^ℓ_+ (p.5)
--   - encoding: h consumers, ℓ goods → 0 < h and 0 < ℓ; reason: [h] and [ℓ] are nonempty in the paper; excludes only the degenerate cases where ε/h or the simplex is undefined
-- source:
--   Barman–Echenique, The Edgeworth Conjecture with Small Coalitions and Approximate Equilibria in Large Economies, arXiv:1905.05165v1, §3, Theorem 3.2 (Main Result), p.8 (standing assumptions §2, pp.5–7; proof §3.3, pp.13–14)

import Mathlib
import Definitions.Def_EdgeworthCore_Model

namespace EdgeworthCore

/-- **Theorem 3.2** (Main Result; Barman–Echenique, arXiv:1905.05165v1, §3, p.8). Let
`E = ((u_i, ω_i))_{i∈[h]}` be an exchange economy with `h ≥ 1` consumers and `ℓ ≥ 1` goods whose
utilities satisfy the standing assumptions of §2 (strictly monotonic, continuously differentiable,
concave, `λ`-Lipschitz, `α`-strongly concave on the balls of radius `r` about the endowments with
`αr² ≥ 2ελℓ/h + 2`, normalized to `[0, 1)` on allocations of `E`), with approximation parameter
`ε > 0`. Suppose that the allocation `x ∈ ℝ^{hℓ}_+` of `E` belongs (replicated) to the κ-core of
`E^n`, where

`n ≥ κ ≥ (16/α)(λℓh/ε + h²/ε²)`.

Then `x` is an ε-Walrasian allocation: there is a price vector `p ∈ Δ` such that `(p, x)` is an
ε-Walrasian equilibrium of `E`.

**Formalization Note.** "`x ∈ ℝ^{hℓ}_+` belongs to the κ-core of `E^n`" is read, as on pp.7–8
(footnote 10), as: the `n`-times replicated allocation `(i, t) ↦ x_t` lies in the κ-core of `E^n`.
In the ε-Walrasian conditions `h` is the number of consumers of `E` (p.6). The standing assumptions
are those of §2 (`StandingAssumptions`), including those not repeated in the theorem's sentence. -/
theorem theorem_3_2 {h ℓ : ℕ} (hh : 0 < h) (hℓ : 0 < ℓ) (E : Economy (Fin h) ℓ)
    (α lam r ε : ℝ) (hε : 0 < ε) (hE : StandingAssumptions E α lam r ε)
    (x : Fin h → Bundle ℓ) (hx : IsAllocation E x) (n κ : ℕ) (hnκ : κ ≤ n)
    (hκ : 16 / α * (lam * ℓ * h / ε + (h : ℝ) ^ 2 / ε ^ 2) ≤ (κ : ℝ))
    (hcore : InKappaCore (replica E n) κ (replicate n x)) :
    ∃ p : Bundle ℓ, IsEpsWalrasianEq E ε p x := by sorry

end EdgeworthCore
