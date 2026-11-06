-- Prove2me | Theorems.Thm_DeepSets_theorem_2_countable
-- name    : DeepSets.theorem_2_countable
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:50:19.773517+00:00
-- url     : https://prove2.me/theorems/a7bab77b-0e77-4fab-83de-9bf62cfcbda5
-- title:
--   Theorem 2 — over a countable universe, a set function is permutation invariant iff $f(X)=\rho\left(\sum_{x\in X}\phi(x)\right)$
-- statement:
--   Let $\mathfrak X$ be a countable universe (finite or countably infinite), and let $f$ assign a real number to every finite set $X=\{x_1,\dots,x_M\}\subseteq\mathfrak X$, presented as a listing of its $M\ge 0$ distinct elements. Then $f$ is a valid set function, that is, permutation invariant (Property 1), if and only if there are functions $\phi:\mathfrak X\to\mathbb R$ and $\rho:\mathbb R\to\mathbb R$ such that
--   $$
--   f(\{x_1,\dots,x_M\}) = \rho\Bigl(\sum_{m=1}^{M}\phi(x_m)\Bigr)
--   $$
--   for every size $M\ge 0$ and every listing of $M$ distinct elements. The same pair $(\phi,\rho)$ serves sets of every size, including the empty set ($f(\emptyset)=\rho(0)$).
--
--   This is the structure theorem behind the Deep Sets architecture: every permutation-invariant function of a finite set over a countable universe is computed by embedding each element with $\phi$, summing, and post-processing with $\rho$.
--
--   **Formalization Note** The universe is a type `U` with `[Countable U]`; a listing of a set is an injective tuple $x:\mathrm{Fin}\,M\to U$ and $f : (M:\mathbb N)\to(\mathrm{Fin}\,M\to U)\to\mathbb R$. No continuity is required of $\phi$ or $\rho$.
--
--   Differences from the source:
--   - reading: |𝔛| < ℵ₀ → [Countable U] (|U| ≤ ℵ₀); reason: p.2 states the theorem for "a countable universe", §2.2 for "𝔛 is a countable set", and the proof uses "since the elements are countable" with c : 𝔛 → ℕ, so < is a slip for ≤; the countable reading is the stronger one and contains the finite case
--   - encoding: a set X = {x₁, …, x_M} with f : 2^𝔛 → ℝ → an injective tuple x : Fin M → U for every M ≥ 0, f : (M : ℕ) → (Fin M → U) → ℝ; reason: Property 1 is stated on listings of a set and is vacuous on an unordered Finset; values on tuples with repeats are unconstrained on both sides
--   - reading: "suitable transformations φ and ρ" → φ : U → ℝ and ρ : ℝ → ℝ, one pair for all M; reason: these are the types the proof constructs (φ(x) = 4^{−c(x)}, "a function ρ : ℝ → ℝ"); requiring them in the necessity direction is the strong reading, and the sufficiency direction holds for them
-- source:
--   Zaheer, Kottur, Ravanbakhsh, Póczos, Salakhutdinov, Smola, Deep Sets, arXiv:1703.06114v3, Theorem 2, p.12 (PDF p.12, §A.1); first stated as Theorem 2, p.2 (§2.2)

import Mathlib
import Definitions.Def_DeepSets_IsPermInvariant

namespace DeepSets

/-- **Theorem 2** (Zaheer et al., *Deep Sets*, arXiv:1703.06114v3, §A.1, p.12; first stated in
§2.2, p.2). Assume the elements are countable. A function `f : 2^𝔛 → ℝ` operating on a set `X`
is a valid set function, i.e. it is permutation invariant to the elements in `X`
(Property 1), if and only if it can be decomposed in the form `ρ(∑_{x ∈ X} φ(x))` for suitable
transformations `φ` and `ρ`.

**Formalization Note**
* The universe `𝔛` is a type `U` with `[Countable U]` (finite or countably infinite). Page 12
  prints `|𝔛| < ℵ₀`, while p.2 says "a countable universe", §2.2 "𝔛 is a countable set" and the
  proof "since the elements are countable" with `c : 𝔛 → ℕ`; the countable reading is the
  stronger one and contains the finite case.
* A set `{x₁, …, x_M}` is an injective tuple `x : Fin M → U`, for every `M ≥ 0`; see
  `DeepSets.IsPermInvariant`.
* `φ : U → ℝ` and `ρ : ℝ → ℝ`, as constructed in the proof (`φ(x) = 4^{-c(x)}`,
  "a function `ρ : ℝ → ℝ`"). No continuity is asked of either.
* The same `φ` and `ρ` serve all set sizes `M` (`∃ φ ρ, ∀ M`). -/
theorem theorem_2_countable {U : Type*} [Countable U] (f : (M : ℕ) → (Fin M → U) → ℝ) :
    IsPermInvariant f ↔
      ∃ φ : U → ℝ, ∃ ρ : ℝ → ℝ, ∀ (M : ℕ) (x : Fin M → U), Function.Injective x →
        f M x = ρ (∑ m, φ (x m)) := by sorry

end DeepSets
