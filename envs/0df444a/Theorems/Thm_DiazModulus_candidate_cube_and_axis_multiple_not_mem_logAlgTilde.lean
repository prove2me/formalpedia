-- Prove2me | Theorems.Thm_DiazModulus_candidate_cube_and_axis_multiple_not_mem_logAlgTilde
-- name    : DiazModulus.candidate_cube_and_axis_multiple_not_mem_logAlgTilde
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T08:51:29.695987+00:00
-- url     : https://prove2.me/theorems/8063a7be-0932-430a-a25d-fa1e80356fc9
-- title:
--   Under the strong six exponentials theorem, a candidate's cube and its products with numbers on an axis are not in ℒ̃
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers, and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Roy's strong six exponentials theorem is carried as the hypothesis `hSSE`: if $x_1, x_2$ are $\overline{\mathbb{Q}}$-linearly independent and so are $y_1, y_2, y_3$, then one of the six products $x_iy_j$ is not in $\widetilde{\mathcal{L}}$.
--
--   Let $u$ be a candidate of Diaz's conjecture: $u \neq 0$, with $|u|$ and $e^u$ algebraic. Then:
--
--   1. $u^3 \notin \widetilde{\mathcal{L}}$;
--   2. $\lambda u \notin \widetilde{\mathcal{L}}$ for every $\lambda \in \widetilde{\mathcal{L}} \setminus \overline{\mathbb{Q}}$ that is real or purely imaginary;
--   3. $e^{\beta\pi u}$ is transcendental for every algebraic $\beta \neq 0$.
--
--   Together with `DiazModulus.candidate_multiplier_module` ($u^2 \notin \widetilde{\mathcal{L}}$), part 1 says that a hypothetical counterexample has neither its square nor its cube in $\widetilde{\mathcal{L}}$.
--
--   **Proof.** Part 1 is Corollaire 5(2) of Diaz (2007) at $\lambda = u$ (`DiazModulus.diaz_2007_cor5`), since $u^2/\bar u = u^3/|u|^2$. Part 2 is Corollaire 2 (P) 2) at $\lambda_2 = u$ (`DiazModulus.diaz_2007_cor2_P_consequences`). Its hypothesis that $1, u, \bar u$ are linearly independent over $\overline{\mathbb{Q}}$ holds at every candidate by Hermite–Lindemann (`DiazModulus.candidate_one_self_conj_linearIndependent`), so Baker's theorem, which Diaz (2004) and Waldschmidt use for general logarithms, is not needed. Part 3 is part 2 at $\lambda = \pi$.
--
--   **Novelty.** None: specialisations of Diaz (2007), Corollaires 5(2) and 2 (P) 2), and of Diaz (2004), Théorème 3(2), which states the transcendence of $e^{\beta\lambda_0\lambda_1}$. The contribution of this node is the formal proof.
-- source:
--   G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Corollaire 5(2) (p. 383) at λ = u, and Corollaire 2 (P) 2) (p. 381) at λ₂ = u; G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, Théorème 3(2) (p. 539); M. Waldschmidt, The role of complex conjugation in transcendental number theory, in: Diophantine Equations (ed. N. Saradha), Narosa, New Delhi, 2008, Theorem 5.1. Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- Under Roy's strong six exponentials theorem, a candidate `u` has `u³ ∉ ℒ̃`; `l * u ∉ ℒ̃` for every
transcendental `l ∈ ℒ̃` on the real or the imaginary axis; and `e^{βπu}` is transcendental for every algebraic
`β ≠ 0`. -/
theorem candidate_cube_and_axis_multiple_not_mem_logAlgTilde
    (hSSE : ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ),
      LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ (∀ i j, x i * y j ∈ LogAlgTilde))
    {u : ℂ} (h : IsCandidate u) :
    u ^ 3 ∉ LogAlgTilde ∧
    (∀ l : ℂ, l ∈ LogAlgTilde → l ∉ Qbar → (l.im = 0 ∨ l.re = 0) → l * u ∉ LogAlgTilde) ∧
    (∀ β : ℂ, IsAlgebraic ℚ β → β ≠ 0 →
      Transcendental ℚ (Complex.exp (β * ((Real.pi : ℝ) : ℂ) * u))) := by
  sorry

end DiazModulus
