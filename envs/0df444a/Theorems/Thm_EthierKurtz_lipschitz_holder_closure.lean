-- Prove2me | Theorems.Thm_EthierKurtz_lipschitz_holder_closure
-- name    : EthierKurtz.lipschitz_holder_closure
-- status  : Proved
-- author  : @caleb
-- created : 2026-10-07T03:02:12.252142+00:00
-- url     : https://prove2.me/theorems/77f2ebdf-b89b-4eac-a1a4-6195627daacf
-- title:
--   Lipschitz maps on bounded regions are Hölder
-- statement:
--   A Lipschitz map on the closure of a bounded region is Hölder continuous with any smaller exponent.
--
--   Let $\Omega$ be bounded and $0 < \mu \le 1$. Every Lipschitz bounded continuous function $h$ on $closure~\Omega$ satisfies a Hölder bound with exponent $\mu$:
--
--   $$
--   |h(x) - h(y)| \le C\, d(x,y)^\mu,
--   $$
--
--   with constant $C$ from the Lipschitz constant and the diameter of the region.
--
--   This is the elementary embedding that makes Lipschitz data admissible for the Hölder-data existence theory; the elliptic existence itself is a separate obligation.
--
--   **Formalization Note** Lean states the conclusion with `HolderWith` (exponent $\mu$ as given) for the coercion of $h$ to a plain function.
-- source:
--   Elementary estimate (Lipschitz implies Hölder on bounded sets); see e.g. Gilbarg--Trudinger, Elliptic Partial Differential Equations of Second Order, Chapter 4 (Hölder spaces).

import Mathlib

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Lipschitz maps on a bounded closed region are Holder: a Lipschitz
bound `K` on `closure Ω` yields a Holder bound with the given exponent
`μ ≤ 1`, with constant from `K` and the diameter of the region. -/
theorem lipschitz_holder_closure (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω)
    (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1) :
    ∀ (h : (closure Ω) →ᵇ ℝ) (K : NNReal),
      LipschitzWith K ⇑h →
        ∃ C : NNReal, HolderWith C ⟨μ, hμ.1.le⟩ ⇑h := by sorry

end EthierKurtz
