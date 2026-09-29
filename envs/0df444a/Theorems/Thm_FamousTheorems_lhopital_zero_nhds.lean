-- Prove2me | Theorems.Thm_FamousTheorems_lhopital_zero_nhds
-- name    : FamousTheorems.lhopital_zero_nhds
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T23:06:17.052986+00:00
-- url     : https://prove2.me/theorems/63bc0cc1-5c6c-47ad-885a-c513d8e5400f
-- title:
--   L'Hôpital's rule
-- statement:
--   **L'Hôpital's rule** for the indeterminate form $0/0$.
--
--   Suppose $f$ and $g$ are differentiable near $a$, that $g' \neq 0$ near $a$, and that
--   $f(x) \to 0$ and $g(x) \to 0$ as $x \to a$. If $f'/g'$ has a limit $l$ at $a$, then
--   $$\lim_{x \to a} \frac{f(x)}{g(x)} = l .$$
--
--   The rule turns an indeterminate quotient into a quotient of derivatives, which is often tractable.
--   The direction matters: a limit for $f'/g'$ gives one for $f/g$, but not conversely — $f/g$ can
--   converge while $f'/g'$ oscillates. The limit $l$ is taken in an arbitrary filter, so the statement
--   covers $l = \pm\infty$ as well as finite limits. The conclusion is stated on the punctured
--   neighbourhood $\mathring{\mathcal{N}}(a)$ because nothing is assumed about $f(a)$ or $g(a)$
--   themselves; indeed $g(a) = 0$ is expected.
--
--   The rule appeared in de l'Hôpital's *Analyse des Infiniment Petits* (1696), the first textbook of
--   differential calculus, but is due to Johann Bernoulli, who had contracted to send his discoveries to
--   l'Hôpital in exchange for a salary.
--
--   **Formalization note.** `∀ᶠ x in 𝓝 a` means "for all $x$ in some neighbourhood of $a$", and `deriv`
--   is the total derivative, which is junk-valued (zero) where $f$ is not differentiable — hence the
--   explicit `DifferentiableAt` hypothesis, without which the statement is false. The result is Mathlib's
--   `deriv.lhopital_zero_nhds`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology

theorem lhopital_zero_nhds {f g : ℝ → ℝ} {a : ℝ} {l : Filter ℝ}
    (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x in 𝓝 a, deriv g x ≠ 0)
    (hfa : Tendsto f (𝓝 a) (𝓝 0)) (hga : Tendsto g (𝓝 a) (𝓝 0))
    (hdiv : Tendsto (fun x => deriv f x / deriv g x) (𝓝 a) l) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) l := by sorry

end FamousTheorems
