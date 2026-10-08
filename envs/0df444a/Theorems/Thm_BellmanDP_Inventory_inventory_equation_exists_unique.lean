-- Prove2me | Theorems.Thm_BellmanDP_Inventory_inventory_equation_exists_unique
-- name    : BellmanDP.Inventory.inventory_equation_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T16:41:59.492857+00:00
-- url     : https://prove2.me/theorems/0ead2f3e-c73e-4027-bb35-b20b5129cc11
-- title:
--   Chapter IV, Theorem 6 (proportional costs) — existence, uniqueness and approximation for the optimal inventory equation
-- statement:
--   Let $k > 0$, $p \ge 0$, $0 < a < 1$, and let $\varphi \ge 0$ on $(0,\infty)$ be integrable with $\int_0^\infty \varphi(s)\,ds = 1$ and $\int_0^\infty ps\,\varphi(s)\,ds < \infty$. These are the conditions (9.4) of Chapter IV for the ordering cost $k(z) = kz$ and the penalty cost $p(z) = pz$. With
--   $$T(y,x,f) = k(y-x) + a\Big[\int_y^\infty p(s-y)\varphi(s)\,ds + f(0)\int_y^\infty \varphi(s)\,ds + \int_0^y f(y-s)\varphi(s)\,ds\Big],$$
--   the following hold.
--
--   1. The equation $f(x) = \inf_{y \ge x} T(y,x,f)$, $x \ge 0$, has exactly one solution among measurable functions bounded on every finite interval $[0,x_0]$ (uniqueness on $[0,\infty)$).
--   2. This solution is continuous on $[0,\infty)$, and for every $x \ge 0$ the infimum is attained, so $f(x) = \min_{y\ge x} T(y,x,f)$.
--   3. For every function $f_0 \ge 0$ continuous on $[0,\infty)$, the approximations $f_{n+1}(x) = \min_{y \ge x} T(y,x,f_n)$ are well defined (each minimum is attained) and $f_n(x) \to f(x)$ for every $x \ge 0$.
--
--   Chapter V's proof of Theorem 1 invokes this result to identify its explicit function as *the* solution.
--
--   **Formalization Note** This restates Chapter IV, Theorem 6 for the proportional costs of Chapter V; the general theorem belongs to the Chapter IV mission of this series. Solutions are required to be measurable.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IV, § 9, Theorem 6, p. 130 (conditions (9.4), p. 130), specialised to k(z) = kz, p(z) = pz as in Chapter V, § 3, p. 158

import Mathlib
import Definitions.Def_BellmanDP_Inventory_Model

open MeasureTheory Filter Topology

namespace BellmanDP.Inventory

/-- Bellman, *Dynamic Programming*, Ch. IV, § 9, Theorem 6, p. 130, for proportional ordering
cost `k(z) = kz` and penalty cost `p(z) = pz` (the case Ch. V, Theorem 1 uses). Under the
conditions (9.4) — `φ ≥ 0`, `∫_0^∞ φ = 1`; `p(s) = ps` monotone increasing and continuous with
`∫_0^∞ p(s) φ(s) ds < ∞`; `k(y) = ky` continuous with `k(∞) = ∞`; `0 < a < 1` — the equation
`f(x) = Inf_{y ≥ x} T(y, x, f)` has exactly one solution (among measurable functions) bounded on
every finite interval `[0, x₀]`; it is continuous on `[0, ∞)` and its infimum is a minimum. For
every non-negative function `f₀` continuous on `[0, ∞)` the approximations
`f_{n+1}(x) = Min_{y ≥ x} T(y, x, f_n)` are well defined (the minimum is attained) and converge
to `f(x)` for every `x ≥ 0`. -/
theorem inventory_equation_exists_unique (k p a : ℝ) (φ : ℝ → ℝ)
    (hk : 0 < k) (hp : 0 ≤ p)
    (hφ_nonneg : ∀ s : ℝ, 0 < s → 0 ≤ φ s) (hφ_int : IntegrableOn φ (Set.Ioi 0))
    (hφ_total : ∫ s in Set.Ioi 0, φ s = 1)
    (hpen : IntegrableOn (fun s => p * s * φ s) (Set.Ioi 0))
    (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ f : ℝ → ℝ, LocallyBoundedClass f ∧ SolvesInf (invT k p a φ) f ∧
      (∀ g : ℝ → ℝ, LocallyBoundedClass g → SolvesInf (invT k p a φ) g →
        Set.EqOn g f (Set.Ici 0)) ∧
      ContinuousOn f (Set.Ici 0) ∧
      (∀ x : ℝ, 0 ≤ x → ∃ y : ℝ, x ≤ y ∧
        IsLeast (invT k p a φ f x '' Set.Ici x) (invT k p a φ f x y)) ∧
      ∀ f₀ : ℝ → ℝ, ContinuousOn f₀ (Set.Ici 0) → (∀ x : ℝ, 0 ≤ x → 0 ≤ f₀ x) →
        (∀ (n : ℕ) (x : ℝ), 0 ≤ x → ∃ y : ℝ, x ≤ y ∧
          IsLeast (invT k p a φ (invIter k p a φ f₀ n) x '' Set.Ici x)
            (invIter k p a φ f₀ (n + 1) x)) ∧
        ∀ x : ℝ, 0 ≤ x → Tendsto (fun n => invIter k p a φ f₀ n x) atTop (𝓝 (f x)) := by sorry

end BellmanDP.Inventory
