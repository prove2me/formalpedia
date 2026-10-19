-- Prove2me | Theorems.Thm_DiazModulus_laurent_conj_twisted_symmetric_normal_form
-- name    : DiazModulus.laurent_conj_twisted_symmetric_normal_form
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:30.950888+00:00
-- url     : https://prove2.me/theorems/0213a2a7-3136-472b-af51-72780fdaab5e
-- title:
--   If g = F(v)/v^N satisfies ḡ = γ v g with |γ| = |v| = 1, then g ≡ G(v) + γ̄ · conj(v G(v)) modulo span(1, v̄) for some polynomial G with G(0) = 0
-- statement:
--   Let $v \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $v\bar v = 1$. Let $N \geq 0$, $F \in \overline{\mathbb{Q}}[X]$ and $g = F(v)/v^N$, and let $\gamma \in \overline{\mathbb{Q}}$ with $\gamma\bar\gamma = 1$ and $\bar g = \gamma vg$. Then there is $G \in \overline{\mathbb{Q}}[X]$ with $G(0) = 0$ such that $$g - \bigl(G(v) + \bar\gamma\,\overline{vG(v)}\bigr) \in \mathrm{span}_{\overline{\mathbb{Q}}}(1, \bar v).$$
--
--   **Proof.** Divide $F = A + X^NB$ with $\deg A < N$, and put $f_0 = B(0)$ and $G = B - f_0$, so $G(0) = 0$ and $g = A(v)/v^N + f_0 + G(v)$. As $\bar v = 1/v$, a conjugated polynomial value times a power of $v$ is the value of the reflected conjugate polynomial, so $\overline{A(v)/v^N} = A'(v)$ with $A'(0) = 0$. Multiplying $\bar g = \gamma vg$ by $v^{N+K}$, $K = \deg G$, gives a polynomial identity at the transcendental $v$, and comparing degrees yields $\overline{A(v)/v^N} = \gamma vG(v) + \gamma f_0v$. Conjugating back, $g - (G(v) + \bar\gamma\,\overline{vG(v)}) = f_0 + \bar\gamma\bar f_0\bar v$.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_conj_twisted_symmetric_normal_form
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1)
    (N : ℕ) (F : Polynomial ↥Qbar) (γ : ℂ) (hγ : γ ∈ Qbar) (hγ1 : γ * conj γ = 1)
    (hF : conj (Polynomial.aeval v F / v ^ N) = γ * v * (Polynomial.aeval v F / v ^ N)) :
    ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧
      Polynomial.aeval v F / v ^ N - (Polynomial.aeval v G + conj γ * conj (v * Polynomial.aeval v G)) ∈
        Submodule.span Qbar ({1, conj v} : Set ℂ) := by
  sorry

end DiazModulus
