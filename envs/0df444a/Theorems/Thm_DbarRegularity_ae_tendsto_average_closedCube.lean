-- Prove2me | Theorems.Thm_DbarRegularity_ae_tendsto_average_closedCube
-- name    : DbarRegularity.ae_tendsto_average_closedCube
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T23:29:16.973741+00:00
-- url     : https://prove2.me/theorems/a0315f95-716f-4066-aa11-6e168aaf487b
-- title:
--   Lebesgue differentiation theorem along shrinking cubes
-- statement:
--   Let $f:\mathbb{R}^d\to E$ be locally integrable, where $E$ is a real Banach space. Then for almost every $x\in\mathbb{R}^d$ the following holds: whenever $(a_j,s_j)_{j}$ is a family of corners and side lengths, indexed along a filter, such that $s_j\to 0^+$ and eventually $x\in Q(a_j,s_j)$, then
--   $$\frac{1}{|Q(a_j,s_j)|}\int_{Q(a_j,s_j)} f(y)\,dy\ \longrightarrow\ f(x),$$
--   where $Q(a,s)=\{y:\ a_i\le y_i\le a_i+s\ \forall i\}$ is the closed cube with corner $a$ and side $s$. The exceptional null set does not depend on the family of cubes.
--
--   This is the Lebesgue differentiation theorem for (not necessarily centred) cubes shrinking to a point, in the form used when a function is compared with its averages over cubes.
--
--   **Formalization Note.** `closedCube a s` comes from `Definitions.Def_DbarRegularity_Setting`; $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`. The average is Mathlib's `⨍ y in Q, f y` (`setAverage`). "Eventually" and the convergence $s_j\to0^+$ (`Tendsto s l (𝓝[>] 0)`) are with respect to an arbitrary filter `l` on an arbitrary index type; the quantifier over `ι`, `l`, `a`, `s` sits inside the almost-everywhere statement.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 1.3, Corollary 1, p. 5

import Definitions.Def_DbarRegularity_Setting

namespace DbarRegularity

open MeasureTheory Filter Topology

/-- Lebesgue differentiation along closed cubes: for a locally integrable `f` on `ℝ^d`, at almost
every `x` the averages of `f` over closed cubes `∏ᵢ [aᵢ, aᵢ + s]` that contain `x` converge to
`f x` as the side length `s` tends to `0⁺`. -/
theorem ae_tendsto_average_closedCube {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : EuclideanSpace ℝ (Fin d) → E}
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, ∀ {ι : Type*} {l : Filter ι} (a : ι → EuclideanSpace ℝ (Fin d)) (s : ι → ℝ),
      Tendsto s l (𝓝[>] 0) → (∀ᶠ j in l, x ∈ closedCube (a j) (s j)) →
      Tendsto (fun j => ⨍ y in closedCube (a j) (s j), f y) l (𝓝 (f x)) := by sorry

end DbarRegularity
