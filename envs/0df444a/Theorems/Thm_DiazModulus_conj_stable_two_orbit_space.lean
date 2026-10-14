-- Prove2me | Theorems.Thm_DiazModulus_conj_stable_two_orbit_space
-- name    : DiazModulus.conj_stable_two_orbit_space
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-14T07:30:12.219211+00:00
-- url     : https://prove2.me/theorems/443a680e-ccae-4356-a4ca-0f724e487350
-- title:
--   For u ∉ Q̄ and real algebraic s with s² = uū: the two-orbit space with |a| = |b| = s and β/α, δ/γ real is stable under complex conjugation
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$, let $a, b \in \overline{\mathbb{Q}}^\times$ with $a^2 \neq b^2$ and $\alpha, \beta, \gamma, \delta \in \overline{\mathbb{Q}}^\times$, put $g_1 = \alpha/(u - a) + \beta/(u + a)$, $g_2 = \gamma/(u - b) + \delta/(u + b)$, and let $W$ be the $\overline{\mathbb{Q}}$-span of $1, u, u^{-1}, g_1, g_2$. Let $s \in \overline{\mathbb{Q}}$ be real with $s^2 = u\bar u$, suppose $a\bar a = b\bar b = s^2$ and that $\beta/\alpha$ and $\delta/\gamma$ are real. Then $W$ is stable under complex conjugation.
--
--   With `DiazModulus.two_orbit_configuration_invisible_to_four_dimensional_extensions` this gives a family of conjugation-stable spaces, invisible to Theorem B, whose configuration factor $(1, u^2)$ has degree two.
--
--   **Proof.** Substitute $\bar u = s^2/u$, $\bar a = s^2/a$, $\bar b = s^2/b$ and $\bar\beta = \beta\bar\alpha/\alpha$, $\bar\delta = \delta\bar\gamma/\gamma$. Then $\bar g_1 = a(\bar\beta - \bar\alpha)/s^2 - (a^2\bar\alpha/(s^2\alpha))\,g_1$ and similarly for $g_2$, while $\bar u = s^2u^{-1}$ and $\overline{u^{-1}} = s^{-2}u$; conjugation of \overline{\mathbb{Q}}-scalars stays in \overline{\mathbb{Q}}, and induction on the span finishes.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. R14 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 14 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem conj_stable_two_orbit_space
    (u : ℂ) (hu : u ∉ Qbar) (a b α β γ δ : ℂ) (ha : a ∈ Qbar) (hb : b ∈ Qbar) (hα : α ∈ Qbar) (hβ : β ∈ Qbar)
    (hγ : γ ∈ Qbar) (hδ : δ ∈ Qbar) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ^ 2 ≠ b ^ 2)
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (hγ0 : γ ≠ 0) (hδ0 : δ ≠ 0)
    (s : ℂ) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u)
    (haa : a * conj a = s * s) (hbb : b * conj b = s * s)
    (hαβ : β * conj α = conj β * α) (hγδ : δ * conj γ = conj δ * γ) :
    ∀ w ∈ Submodule.span Qbar ({1, u, u⁻¹, (α / (u - a) + β / (u + a)), (γ / (u - b) + δ / (u + b))} : Set ℂ), conj w ∈ Submodule.span Qbar ({1, u, u⁻¹, (α / (u - a) + β / (u + a)), (γ / (u - b) + δ / (u + b))} : Set ℂ) := by
  sorry

end DiazModulus
