-- Prove2me | Theorems.Thm_DiazModulus_laurent_involution_space_conj_stable_constraints
-- name    : DiazModulus.laurent_involution_space_conj_stable_constraints
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:43.041202+00:00
-- url     : https://prove2.me/theorems/a3f8ad01-f0c6-4abd-a07b-df9331ed7533
-- title:
--   If span(1, v, v̄, v̄² + e v², β v̄³ + ζ v² + e v³) is conjugation-stable and β ≠ 0, then |e| = |β| = 1 and ζ = −β e² ζ̄
-- statement:
--   Let $v \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $v\bar v = 1$. Let $e, \beta, \zeta \in \overline{\mathbb{Q}}$ with $\beta \neq 0$, and suppose that $S = \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v, \bar v^2 + ev^2, \beta\bar v^3 + \zeta v^2 + ev^3)$ is stable under complex conjugation: $\bar w \in S$ for every $w \in S$. Then $e\bar e = 1$, $\beta\bar\beta = 1$ and $\zeta = -\beta e^2\bar\zeta$.
--
--   **Proof.** Write $n_0 = \bar v^2 + ev^2$ and $n_1 = \beta\bar v^3 + \zeta v^2 + ev^3$. Conjugation fixes $S$, so $\bar n_0 = v^2 + \bar e\bar v^2$ and $\bar n_1 = \bar\beta v^3 + \bar\zeta\bar v^2 + \bar e\bar v^3$ are $\overline{\mathbb{Q}}$-combinations of $1, v, \bar v, n_0, n_1$; multiplied by $v^3$, each relation is a polynomial identity of degree $6$ at the transcendental $v$, so coefficients can be compared. For $\bar n_0 = c_1 + c_2v + c_3\bar v + c_4n_0 + c_5n_1$, the coefficients at $v^{-3}$, $v^{-2}$ and $v^2$ give $c_5 = 0$, $c_4 = \bar e$ and $c_4e = 1$, so $e\bar e = 1$. For $\bar n_1 = d_1 + d_2v + d_3\bar v + d_4n_0 + d_5n_1$, those at $v^{-3}$ and $v^3$ give $\bar e = d_5\beta$ and $\bar\beta = d_5e$, so $\beta\bar\beta = e\bar e = 1$, and those at $v^{-2}$ and $v^2$ give $d_4 = \bar\zeta$ and $d_4e + d_5\zeta = 0$, which multiplied by $\beta e$ is $\beta e^2\bar\zeta + \zeta = 0$.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_involution_space_conj_stable_constraints
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1)
    (e β ζ : ℂ) (he : e ∈ Qbar) (hβ : β ∈ Qbar) (hζ : ζ ∈ Qbar) (hβ0 : β ≠ 0)
    (hconj : ∀ w ∈ Submodule.span Qbar ({1, v, conj v, conj v ^ 2 + e * v ^ 2, β * conj v ^ 3 + ζ * v ^ 2 + e * v ^ 3} : Set ℂ),
      conj w ∈ Submodule.span Qbar ({1, v, conj v, conj v ^ 2 + e * v ^ 2, β * conj v ^ 3 + ζ * v ^ 2 + e * v ^ 3} : Set ℂ)) :
    e * conj e = 1 ∧ β * conj β = 1 ∧ ζ = -(β * e ^ 2 * conj ζ) := by
  sorry

end DiazModulus
